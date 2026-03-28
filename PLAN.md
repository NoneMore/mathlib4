# `ModelTheory` Constant-Expansion Refactor Plan

## Findings

1. The core language-level definition is already fine.
   In `Mathlib/ModelTheory/LanguageMap.lean`,
   `Language.withConstants` is still
   `L.sum (constantsOn α)`;
   `lhomWithConstants`, `withConstantsStructure`, and `withConstants_expansion`
   are already present and usable.

2. The existing type-synonym technique is only used along one narrow path.
   At the moment, `LanguageMap.lean` only uses a real type synonym in
   `Embedding.withConstants : Type := N`,
   where the point is to attach an `L[[A]]`-structure to the same underlying carrier via a parameter-dependent interpretation.
   `ElementaryEmbedding.liftWithConstants` merely reuses that construction.

3. The current burden splits into two separate categories.
   - Inside proofs, we manually install
     `letI : (constantsOn α).Structure M := constantsOn.structure v`
     or `haveI`.
   - In theorem statements, we directly require
     `[L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M]`,
     even when the theorem is really about “given `v : α → M`, regard `M` as the corresponding constant expansion”.

4. The first category is currently concentrated in the following places.
   - `Formula.realize_equivSentence_symm`
     in `Mathlib/ModelTheory/Semantics.lean`
   - `Theory.typeOf`
     in `Mathlib/ModelTheory/Types.lean`
   - `CompleteType.mem_typeOf`
     in `Mathlib/ModelTheory/Types.lean`
   - `isSatisfiable_union_distinctConstantsTheory_of_card_le`
     in `Mathlib/ModelTheory/Satisfiability.lean`
   - `models_formula_iff_onTheory_models_equivSentence`
     in `Mathlib/ModelTheory/Satisfiability.lean`
   - `ModelsBoundedFormula.realize_formula`
     in `Mathlib/ModelTheory/Satisfiability.lean`

5. The second category mainly appears in the constant/variable semantic transport lemmas in `Semantics.lean`.
   Those theorems currently take an arbitrary `L[[α]]`-structure as input:
   - `Term.realize_constantsToVars`
   - `Term.realize_varsToConstants`
   - `Term.realize_constantsVarsEquivLeft`
   - `BoundedFormula.realize_constantsVarsEquiv`
   - `Formula.realize_equivSentence_symm_con`
   - `Formula.realize_equivSentence`

6. `constantsOnMap_isExpansionOn` in `LanguageMap.lean` (line 364) also uses
   `letI := constantsOn.structure fα` / `letI := constantsOn.structure fβ`.
   This is not a valuation-driven constant-expansion, but rather a proof about compatibility
   of two `constantsOn` structures under a map `f : α → β`.
   It should not be forced into the new synonym, but it should be explicitly acknowledged
   as out-of-scope for this refactor.

7. Not every explicit instance should be eliminated.
   The following results genuinely speak about an arbitrary `L[[α]]`-model, not “the expansion induced by some given valuation `v`”:
   - `model_distinctConstantsTheory`
     and `card_le_of_model_distinctConstantsTheory`
     in `Semantics.lean`
   - `ElementaryEmbedding.ofModelsElementaryDiagram`
     in `ElementaryMaps.lean`
   Those APIs should remain generic and should not be forced into valuation-specific form.

8. There is another pain point in `Satisfiability.lean` that is related but not identical to this refactor:
   after
   `letI := (L.lhomWithConstants α).reduct M`,
   `IsExpansionOn_reduct` still sometimes needs a manual `have`.
   That is a reduct-side instance-resolution issue, not a valuation-driven constant-expansion issue.
   The first pass of this refactor should not tie those two problems together.

## Goals

1. Introduce a general type synonym determined by `v : α → M`,
   so that “the constant expansion of `M`” is represented by a dedicated type rather than by locally installing instances on bare `M`.

2. Use that synonym to eliminate valuation-related
   `letI : (constantsOn α).Structure M := ...`
   and ugly terms of the form
   `@Language.withConstantsStructure ... (constantsOn.structure v)`
   from the `ModelTheory` module.

3. Preserve the low-level generic API.
   Wherever the mathematics genuinely needs an arbitrary `L[[α]]`-structure,
   keep the
   `[L[[α]].Structure M]` /
   `[(L.lhomWithConstants α).IsExpansionOn M]`
   versions rather than forcing an immediate signature rewrite.

4. Make `Embedding.withConstants` a special case of the new general synonym,
   so that the logic for attaching parameterized `L[[α]]`-structures to a fixed carrier is centralized in one implementation.

## Core Design

### 1. Add a general synonym in `LanguageMap.lean`

Add a definition in the `FirstOrder.Language` namespace with shape similar to:

```lean
@[nolint unusedArguments]
def ConstantsExpansion {M : Type w} [L.Structure M] {α : Type w'}
    (_v : α → M) : Type w := M
```

Key points:

- Use `def`, not `abbrev`.
  We want a genuinely different head symbol so that different valuations produce distinct instance keys.
- This definition belongs in `LanguageMap.lean`, since it is infrastructure for constant expansions.
  Putting it in `Semantics.lean` would invert the dependency direction.
- Do not introduce new notation.
  This should remain a lightweight internal mechanism, not additional surface syntax.

#### Universe consistency with `Embedding.withConstants`

`ConstantsExpansion` returns `Type w`, the same universe as `M` (the carrier that `v` maps into).
`Embedding.withConstants (f : M ↪[L] N) (A : Set M)` returns `Type w'`, the universe of `N`.
These are consistent because in the embedding case, the valuation is
`fun a : A => f a : ↑A → N`, so the carrier is `N : Type w'` and `ConstantsExpansion`
returns `Type w'` accordingly (since the `w` in `ConstantsExpansion` unifies with `w'` of `N`).

### 2. Provide the standard instances for the synonym

At minimum, add the following instances:

```lean
instance : L.Structure (L.ConstantsExpansion v) := by
  dsimp [Language.ConstantsExpansion]
  infer_instance

instance : (constantsOn α).Structure (L.ConstantsExpansion v) :=
  constantsOn.structure v

instance : L[[α]].Structure (L.ConstantsExpansion v) :=
  L.withConstantsStructure α

instance : (L.lhomWithConstants α).IsExpansionOn (L.ConstantsExpansion v) :=
  L.withConstants_expansion α
```

#### Instance resolution chain

The expected instance resolution path for `L.ConstantsExpansion v` is:

1. `L.Structure (L.ConstantsExpansion v)` — unfolds to the existing `L.Structure M`.
2. `(constantsOn α).Structure (L.ConstantsExpansion v)` — resolves to `constantsOn.structure v` (provided directly).
3. `L[[α]].Structure (L.ConstantsExpansion v)` — resolves via `L.withConstantsStructure α`,
   which combines (1) and (2) through `Language.Sum.instStructure`.
4. `(L.lhomWithConstants α).IsExpansionOn (L.ConstantsExpansion v)` — resolves via `L.withConstants_expansion α`,
   which depends on (3).

Since the chain is short (each step is one hop), Lean's instance search should handle it
without difficulty. If any step fails, the symptom will be a `failed to synthesize` error
mentioning the exact missing link. In that case, provide the instance explicitly rather than
lengthening the chain.

Also add the minimal set of genuinely useful `@[simp]` bridge lemmas, for example:

```lean
@[simp] theorem con_eq {a : α} :
    (L.con a : L.ConstantsExpansion v) = v a := rfl
```

If later proofs repeatedly need to move between the synonym and the original `M`,
add only the few `rfl`-level lemmas that are actually needed.
Do not add a large batch of speculative coercions.

However, include the following minimal bridging pair from the start,
since proofs will almost certainly need to pass values between `M` and the synonym:

```lean
/-- View an element of `M` as an element of the constant expansion. -/
def ConstantsExpansion.mk (x : M) : L.ConstantsExpansion v := x

/-- View an element of the constant expansion as an element of `M`. -/
def ConstantsExpansion.val (x : L.ConstantsExpansion v) : M := x

@[simp] theorem ConstantsExpansion.val_mk (x : M) :
    (ConstantsExpansion.mk v x).val v = x := rfl
```

Add further coercions or `Equiv`s only if downstream proofs demand them.

### 3. Make `Embedding.withConstants` reuse the new core

Refactor
`Embedding.withConstants (f : M ↪[L] N) (A : Set M)`
to become a special case of the general synonym, preferably as:

```lean
abbrev Embedding.withConstants (f : M ↪[L] N) (A : Set M) :=
  (L := L).ConstantsExpansion (fun a : A => f a)
```

If turning it directly into an `abbrev` causes too much elaboration churn,
keep the public outer definition but delegate all internal instances to the general synonym.
Concretely, the fallback is:

```lean
-- Keep as an opaque def:
@[nolint unusedArguments]
def Embedding.withConstants (_f : M ↪[L] N) (_A : Set M) : Type w' := N

-- But delegate all instances via definitional equality:
instance : L.Structure (f.withConstants A) :=
  (inferInstance : L.Structure (L.ConstantsExpansion fun a : A => f a))

instance : (constantsOn A).Structure (f.withConstants A) :=
  (inferInstance : (constantsOn A).Structure (L.ConstantsExpansion fun a : A => f a))

-- ... and so on for L[[A]].Structure and IsExpansionOn
```

Also add a `@[simp]` lemma unifying the two when needed:

```lean
@[simp] theorem Embedding.withConstants_eq (f : M ↪[L] N) (A : Set M) :
    f.withConstants A = L.ConstantsExpansion (fun a : A => f a) := rfl
```

Do not maintain a second parallel copy of the
`L.Structure` / `constantsOn` / `L[[A]]`
instance stack.

### 4. Add valuation-facing semantic wrappers

The new synonym solves the problem of obtaining a canonical expanded model from a valuation.
To make downstream theorem statements cleaner, we also need a thin wrapper layer.

The highest-priority target is replacing goals like:

```lean
@Sentence.Realize _ M
  (@Language.withConstantsStructure L M _ α (constantsOn.structure v)) φ
```

with statements phrased as “evaluate in `L.ConstantsExpansion v`”.

If
`@Sentence.Realize _ (L.ConstantsExpansion v) _ φ`
is already readable enough, use it directly.
If not, add a very thin helper such as:

```lean
def Sentence.RealizeWithConstants (φ : L[[α]].Sentence) (v : α → M) : Prop :=
  @Sentence.Realize _ (L.ConstantsExpansion v) _ φ
```

Likewise, add `realizeWithConstants` / `RealizeWithConstants` wrappers for `Term` or `BoundedFormula`
only if they materially improve theorem statements.

## File-by-File Execution Plan

### Step 1: `Mathlib/ModelTheory/LanguageMap.lean`

1. Add the general synonym and its 4 core instances.
2. Add 1 to 3 genuinely useful `@[simp]` lemmas for the synonym.
3. Refactor `Embedding.withConstants` into a special case of the general synonym, or minimally delegate it to the new implementation.
4. Recheck whether
   - `Embedding.liftWithConstants`
   - `ElementaryEmbedding.liftWithConstants`
   - `withConstants_funMap_sumInr`
   still go through with `rfl`, `simp`, and at most a small amount of `change`.

After this step, run file-level verification:

```bash
lake env lean Mathlib/ModelTheory/LanguageMap.lean
lake env lean Mathlib/ModelTheory/ElementaryMaps.lean
```

### Step 2: `Mathlib/ModelTheory/Semantics.lean`

The strategy here is: keep the generic low-level theorems, add valuation-facing wrappers.

Keep the original signatures of:

- `withConstants_funMap_sumInl`
- `withConstants_relMap_sumInl`
- `realize_constantsToVars`
- `realize_varsToConstants`
- `realize_constantsVarsEquivLeft`
- `realize_constantsVarsEquiv`
- `realize_equivSentence_symm_con`
- `realize_equivSentence`

These results genuinely describe semantics in an arbitrary expanded structure, so they should not be rewritten on the first pass.

But add or rewrite a valuation-facing layer:

1. Rewrite `Formula.realize_equivSentence_symm`
   so that it no longer mentions
   `@Language.withConstantsStructure ... (constantsOn.structure v)`.

2. If useful, add wrappers analogous to:
   - `Term.realize_constantsToVars_of_constantsExpansion`
   - `Term.realize_varsToConstants_of_constantsExpansion`
   - `BoundedFormula.realize_constantsVarsEquiv_of_constantsExpansion`

The exact names are not important.
What matters is:

- the theorem statement only quantifies over `v : α → M`,
  without requiring the caller to manually provide `[L[[α]].Structure M]`;
- the proof uses the new synonym instances directly,
  without `letI : (constantsOn α).Structure M := ...`.

After this step, verify:

```bash
lake env lean Mathlib/ModelTheory/Semantics.lean
```

### Step 3: `Mathlib/ModelTheory/Types.lean`

This file should benefit most directly.

Required changes:

1. `Theory.typeOf`
   currently installs
   `haveI : (constantsOn α).Structure M := constantsOn.structure v`
   and then takes `L[[α]].completeTheory M`.
   Rewrite it to take the complete theory of `L.ConstantsExpansion v` directly.

2. `CompleteType.mem_typeOf`
   currently depends on a local `letI` in order to apply
   `Formula.realize_equivSentence_symm`.
   Rewrite it to use the new valuation-facing wrapper.

3. `Theory.exists_modelType_is_realized_in`
   probably does not need a major rewrite.
   Keep the current generic proof unless the new wrapper makes it materially shorter.

After this step, verify:

```bash
lake env lean Mathlib/ModelTheory/Types.lean
```

### Step 4: `Mathlib/ModelTheory/Satisfiability.lean`

This file needs to be split into two subproblems.

#### 4a. Replace local `constantsOn.structure` uses with the synonym

Refactor the following sites:

1. `isSatisfiable_union_distinctConstantsTheory_of_card_le`
   Replace the witness model from “bare `M` with locally installed instances”
   to the actual type `L.ConstantsExpansion v`.

2. The reverse implication in `models_formula_iff_onTheory_models_equivSentence`.
   This branch is exactly “given `v`, regard `M` as a model with those parameter constants”,
   so it should use the synonym directly.

3. `ModelsBoundedFormula.realize_formula`
   should also be rewritten to use the new valuation-facing wrapper.

#### 4b. Temporarily keep the reduct-side manual instance

In the forward implication of
`models_formula_iff_onTheory_models_equivSentence`,
the pattern

```lean
letI := (L.lhomWithConstants α).reduct M
have : (L.lhomWithConstants α).IsExpansionOn M := ...
```

is not the primary target of this synonym refactor.
If that explicit `have` is still needed after 4a is complete,
leave it in place rather than trying to “clean it up” by changing global `IsExpansionOn_reduct` behavior.

After this step, verify:

```bash
lake env lean Mathlib/ModelTheory/Satisfiability.lean
```

### Step 5: `Mathlib/ModelTheory/ElementaryMaps.lean`

This is mainly consistency cleanup.

1. Confirm that `ElementaryEmbedding.liftWithConstants`
   still works after `Embedding.withConstants` is refactored into a special case of the general synonym.

2. Keep `ElementaryEmbedding.ofModelsElementaryDiagram`
   generic.
   It really does require an arbitrary `L[[M]]`-model, so it should not be rewritten into a valuation-specific API just to reduce local instance noise.

After this step, verify again:

```bash
lake env lean Mathlib/ModelTheory/ElementaryMaps.lean
```

## Compatibility Strategy

1. On the first pass, do not rename the existing generic theorems.
   Add valuation-facing wrappers first, then migrate internal module call sites to those wrappers.

2. Only consider a second-pass API cleanup if both conditions hold:
   - the new wrappers cover all valuation-driven use cases that users actually need;
   - the old generic names have become actively misleading.

3. Preserve the public name `Embedding.withConstants`.
   Even if the implementation changes internally, downstream code should not need to care.

## Audit Checklist

After each migration phase, run:

```bash
rg -n "letI\s*:.*constantsOn|letI\s*:=\s*constantsOn\.structure|haveI\s*:.*constantsOn|@Language\.withConstantsStructure|constantsOn\.structure\s+\w" Mathlib/ModelTheory
```

The intended outcome is:

- no valuation-local `constantsOn.structure` remains in `Types.lean`;
- only reduct-side explicit instances remain in `Satisfiability.lean`, and only where intentionally allowed;
- `Semantics.lean` no longer contains
  `@Language.withConstantsStructure ... (constantsOn.structure v)`;
- `constantsOnMap_isExpansionOn` in `LanguageMap.lean` retains its `letI` uses
  (they are out-of-scope for this refactor).

Also audit public theorem assumptions involving expanded-language structures:

```bash
rg -n "\\[L\\[\\[[^]]+\\]\\]\\.Structure|\\(L\\.lhomWithConstants .*\\)\\.IsExpansionOn" Mathlib/ModelTheory
```

Audit standard:

- keep genuinely generic results generic;
- for purely valuation-facing results, add or migrate to wrappers.

## Final Verification

Run file-level checks in dependency order:

```bash
lake env lean Mathlib/ModelTheory/LanguageMap.lean
lake env lean Mathlib/ModelTheory/Semantics.lean
lake env lean Mathlib/ModelTheory/Types.lean
lake env lean Mathlib/ModelTheory/Satisfiability.lean
lake env lean Mathlib/ModelTheory/ElementaryMaps.lean
```

If those pass, run module-level builds:

```bash
lake build Mathlib.ModelTheory.LanguageMap
lake build Mathlib.ModelTheory.Semantics
lake build Mathlib.ModelTheory.Types
lake build Mathlib.ModelTheory.Satisfiability
lake build Mathlib.ModelTheory.ElementaryMaps
```

If the refactor touches files beyond those five, add corresponding `lake env lean` checks and then run one final `lake build`.

### Downstream Impact Check

Before final verification, check whether any files outside `Mathlib/ModelTheory/`
depend on the refactored APIs:

```bash
rg -l "Embedding\.withConstants|constantsOn\.structure|withConstantsStructure" Mathlib --glob '!Mathlib/ModelTheory/**'
```

If matches are found, verify those files also compile after the refactor.

## Done Criteria

This refactor is complete when all of the following hold:

1. There is a general valuation-driven type synonym,
   and `Embedding.withConstants` either reuses it directly or gets all of its instances from it.

2. The valuation-related
   `letI : (constantsOn α).Structure M := ...`
   patterns in `Types.lean` and `Satisfiability.lean`
   have been eliminated.

3. `Semantics.lean` contains clean valuation-facing wrappers,
   and no longer exposes
   `@Language.withConstantsStructure ... (constantsOn.structure v)`.

4. Genuinely generic expanded-language APIs remain intact,
   and have not been incorrectly collapsed into valuation-only forms.

5. All affected files pass `lake env lean`,
   and the module-level `lake build` checks pass.
