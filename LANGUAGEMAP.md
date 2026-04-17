# Refactor Plan for `Mathlib/ModelTheory/LanguageMap.lean`

## Survey Summary

The current `Mathlib/ModelTheory/LanguageMap.lean` already provides three core layers:

- `LHom` / `LEquiv`, together with `reduct`, `sumInl`, `sumInr`, `sumElim`, and `sumMap`
- The constant language `constantsOn α` and the expanded language `L[[α]]`
- Several structure instances and utilities related to constant expansions, including
  `lhomWithConstants`, `lhomWithConstantsMap`, and `Embedding.liftWithConstants`

The main downstream modules that directly depend on this API are:

- `Mathlib/ModelTheory/Syntax.lean`: `onTerm`, `onBoundedFormula`, `constantsVarsEquiv`,
  `equivSentence`
- `Mathlib/ModelTheory/Semantics.lean`: syntactic/semantic transport,
  `realize_equivSentence`, `LHom.onTheory_model`
- `Mathlib/ModelTheory/Definability.lean`: `Definable.map_expansion`, `Definable.mono`
- `Mathlib/ModelTheory/Types.lean`: `CompleteType`, `typeOf`
- `Mathlib/ModelTheory/Satisfiability.lean`: satisfiability and parameter theories
- `Mathlib/ModelTheory/Substructures.lean`: `Substructure.withConstants`
- `Mathlib/ModelTheory/ElementaryMaps.lean`: `ElementaryEmbedding.liftWithConstants`

One further structural observation is important for the refactor scope:

- The existing type-synonym technique is currently only used along one narrow path,
  namely `Embedding.withConstants`, and `ElementaryEmbedding.liftWithConstants` simply reuses it.
- By contrast, many other uses of constant expansion still proceed by installing local instances on
  the bare carrier.
- At the same time, some APIs genuinely need to talk about an arbitrary expanded-language model,
  and should not be rewritten into valuation-specific form merely for uniformity.

In addition, `~/working_directory/StabilityTheory/StabilityTheory/ModelTheory/LanguageMap.lean`
already contains a batch of natural API extensions that are missing upstream:

- `LHom.id_sumMap_id`
- `LHom.sumMap_comp_sumMap`
- `LHom.constantsOnMap_comp`
- `LHom.constantsOnMap_id`
- `LHom.addConstants_comp_lhomWithConstants`
- `LHom.onTheory_lhomWithConstants`
- `LEquiv.withConstantsCongr`
- `LEquiv.addConstants`
- `LEquiv.toLHom_addConstants`

These lemmas indicate that the main weakness of the current `withConstants` design is not that
definitions are absent, but that the functoriality and compatibility API is incomplete.

## Current Pain Points

1. Carrier-side packaging of constant interpretations is inconsistent.
   At present, `Embedding.withConstants` only handles the specific situation where constants for
   `A : Set M` are interpreted in another model along an embedding. Meanwhile, files such as
   `Semantics.lean`, `Satisfiability.lean`, and `Types.lean` still repeatedly rely on local
   instances of the form
   `letI : (constantsOn α).Structure M := constantsOn.structure v`.

2. The functorial API for `sum` and `withConstants` is incomplete.
   The file currently has `sumMap_comp_inl` and `sumMap_comp_inr`, but it lacks structural lemmas
   such as “composition is computed componentwise” and “identity is computed componentwise”, so
   downstream files keep reproving these facts manually.

3. The `LEquiv` layer lacks a standard interface saying that language equivalences lift through
   adjoining constants.
   This blocks a systematic transport of language equivalences to sentences, theories, complete
   types, and similar objects.

4. There is still a gap between syntactic transport and semantic transport.
   `Syntax.lean` and `Semantics.lean` already contain many results about `onTerm`,
   `realize_onFormula`, and `onTheory_model`, but the compatibility of these constructions with
   `addConstants`, `lhomWithConstantsMap`, and reindexing of parameters is not expressed in a
   systematic way.

5. Parameter expansion is already type-general at the language level, but the user-facing API still
   leans heavily toward `A : Set M`.
   As a result, some interfaces are forced to work through subtypes and inclusions rather than
   directly through arbitrary maps `α → M` or embeddings `α ↪ M`.

6. There are really two different problems mixed together in the current codebase.
   One is valuation-driven constant expansion: given `v : α → M`, regard `M` as an
   `L[[α]]`-structure in a canonical way. The other is the genuinely generic study of arbitrary
   `L[[α]]`-structures and expansions. The refactor should improve the first without collapsing the
   second into a more specialized interface.

7. Some related instance-resolution annoyances should be kept separate from this refactor.
   In particular, reduct-side issues involving `IsExpansionOn_reduct` are adjacent in spirit, but
   they are not the same problem as valuation-driven constant expansion and should not determine the
   design of the first pass.

## Additional Design Goals

In addition to the four goals already listed by the user, the following goals should be added.

1. Treat “a chosen interpretation of constants” as a first-class object.
   Concretely, introduce a carrier-level type synonym parameterized by `v : α → M`, packaging the
   non-canonical instances for `(constantsOn α).Structure` and `L[[α]].Structure`. Then
   `Embedding.withConstants` should become either a special case or a thin wrapper around this more
   general construction.

2. Make `withConstants` explicitly bifunctorial.
   One side varies with language maps, the other with reindexing maps on the parameter type.
   `LHom.addConstants`, `LHom.constantsOnMap`, and `LEquiv.withConstantsCongr` should be part of
   one coherent design rather than isolated utilities.

3. Preserve the subset-based API as an easy wrapper for downstream users.
   Interfaces with `A : Set M` should remain available, since `Definability`, `Substructures`, and
   `ElementaryMaps` currently use them as the main user-facing entry point. However, their
   implementation should reduce to the more general parameter-type version.

4. Make explicit that language equivalences lift across constant expansions.
   This supports `LanguageMap` itself, and also prepares the ground for comparing `L[[M]]` with
   `L[[(Set.univ : Set M)]]`, transporting complete theories, and transporting complete types.

5. Control the direction of the simp API.
   Only genuinely stable, one-way compatibility lemmas should receive `[simp]`. In particular,
   lemmas involving `sumMap`, `comp`, and `withConstantsCongr` should be designed to avoid rewrite
   loops.

6. Preserve the distinction between valuation-facing APIs and genuinely generic expanded-language
   APIs.
   Results whose mathematics is really “given `v : α → M`, evaluate in the corresponding constant
   expansion” should gain a canonical valuation-facing formulation. Results whose mathematics is
   genuinely about arbitrary `L[[α]]`-models should remain generic.

7. Centralize the carrier-level implementation of parameterized expansions.
   The new valuation-driven packaging should become the common mechanism behind
   `Embedding.withConstants`, rather than introducing a second parallel approach.

8. Explicitly mark some nearby issues as out of scope for the first pass.
   In particular, compatibility proofs such as `constantsOnMap_isExpansionOn`, and reduct-side
   instance search issues around `IsExpansionOn_reduct`, should not be forced into the same design
   bucket unless they naturally simplify afterward.

## Concrete Implementation Plan

### Phase A: Complete the algebraic API for `LHom` and `LEquiv`

Goal: first upstream the pure API gaps that are already validated in the reference repository,
while avoiding downstream definition changes.

First batch of declarations that should likely go upstream directly:

- `LHom.funext_iff` or an equivalent `LHom.ext_iff`
- `LHom.id_sumMap_id`
- `LHom.sumMap_comp_sumMap`
- `LHom.constantsOnMap_comp`
- `LHom.constantsOnMap_id`
- `LHom.addConstants_comp_lhomWithConstants`
- `LHom.onTheory_lhomWithConstants`
- `LEquiv.withConstantsCongr`
- `LEquiv.addConstants`
- `LEquiv.toLHom_addConstants`

Second batch, depending on actual usage frequency:

- `LEquiv.toLHom_injective`
- `LEquiv.invLHom_injective`
- Further compatibility lemmas relating `sumElim` and `sumMap`
- Specialized versions at the `onTerm` / `onFormula` / `onSentence` level

Expected benefits:

- `LanguageMap.lean` itself becomes expressive enough to describe “sum maps and composition” and
  “constant expansion and composition” as standard categorical structure
- The patch-style `LanguageMap.lean` in `StabilityTheory` can be deleted
- A uniform foundation is established for later `univ` comparisons and transport constructions

### Phase B: Introduce a general type synonym for constant interpretations

Goal: eliminate the scattered pattern
`letI : (constantsOn α).Structure M := ...`
from multiple files.

Suggested approach:

- Introduce a general synonym inside `LanguageMap.lean`, parameterized by something like
  `v : α → M`
- Give this synonym canonical instances for
  `[(constantsOn α).Structure _]` and `[L[[α]].Structure _]`
- Rewrite the current `Embedding.withConstants` as a special case of this general synonym, so that
  there are not two parallel packaging strategies

At the design level, this phase should be understood as introducing a canonical carrier-level
representation of valuation-driven constant expansion. The point is not just to reduce local
instance noise, but to make the phrase “the expansion induced by `v : α → M`” correspond to a
single standard object throughout the library.

The first downstream use sites that should be migrated:

- `Mathlib/ModelTheory/Semantics.lean`
- `Mathlib/ModelTheory/Types.lean`
- `Mathlib/ModelTheory/Satisfiability.lean`

Design requirements:

- The synonym should stay as definitional-equality-friendly as possible, so that existing `rfl`
  proofs are not broken unnecessarily
- Its name should avoid confusion with the existing `Language.withConstants`
- Instance priorities must be chosen carefully to avoid ambiguity or loops with the current
  `withConstantsStructure`

This phase should not attempt to absorb every use of explicit `constantsOn.structure`.
Some appearances, especially those proving compatibility between two different constant-language
structures under a reindexing map, belong to a different layer of abstraction and may reasonably
remain outside the new synonym.

### Phase C: Promote parameter expansion from a subtype-based special case to a general interface

Goal: make “parameter language + interpretation map” the primary interface, with `A : Set M` only
as a derived entry point.

Suggested direction:

- Treat the parameter collection uniformly as an arbitrary type `α`
- Treat interpretation of parameters in a model uniformly as an arbitrary map `v : α → M`
- View the case `A : Set M` as the special case `α := A`, `v := Subtype.val`

Accordingly, the following existing interfaces should be reorganized into “general version +
subset version”:

- `paramsStructure`
- `constantsOnMap_isExpansionOn`
- `lhomWithConstantsMap`
- `map_constants_inclusion_isExpansionOn`
- `Substructure.withConstants`
- `Embedding.liftWithConstants`
- `ElementaryEmbedding.liftWithConstants`

The key point here is not to rewrite all definitions immediately, but first to generalize the
underlying transport API so that the subset-based wrappers become routine.

### Phase D: Systematically fill in the syntactic and semantic transport lemmas

Goal: make explicit the compatibility that is currently only implicit between `LanguageMap.lean`
and `Syntax` / `Semantics`.

Highest-priority directions:

- compatibility of `addConstants` with `onTerm`, `onBoundedFormula`, `onFormula`, `onSentence`
- compatibility of `lhomWithConstantsMap` with the `realize_*` family of lemmas
- compatibility of constant reindexing (`constantsOnMap`) with transport of sentences and theories
- companion rewrite lemmas for `LEquiv.withConstantsCongr` at the `onSentence` / `onTheory` level

Files that benefit most from this migration:

- `Mathlib/ModelTheory/Semantics.lean`
- `Mathlib/ModelTheory/Definability.lean`
- `Mathlib/ModelTheory/Types.lean`
- `Mathlib/ModelTheory/Satisfiability.lean`

This phase should include a valuation-facing wrapper layer for the main semantic constructions,
while deliberately keeping the low-level generic theorems intact. In other words, the intended
outcome is not to replace all generic statements by valuation-specific ones, but to add a cleaner
canonical entry point for the valuation-driven use case and migrate internal call sites to it where
appropriate.

### Phase E: Optional later extensions

This does not need to be part of the first refactor pass, but the refactor should leave room for
it:

- a canonical `LEquiv` comparing `L[[M]]` and `L[[(Set.univ : Set M)]]`
- API for transporting complete theories, complete types, and partial types
- upstreaming the ideas from `StabilityTheory/ModelTheory/LanguageMapOnUniv.lean`

If Phases A and B are designed well, these extensions should require only a small number of new
definitions rather than another round of foundational lemmas.

## Recommended PR Splitting

To align with Mathlib’s preference for small, self-contained PRs, this should not be attempted as
one large refactor. A better split is:

1. Pure `LanguageMap` API strengthening.
   Add only lemmas and `LEquiv` / `LHom` functorial interfaces, without changing downstream files.

2. General constant-interpretation synonym.
   Introduce the new carrier-level wrapper in `LanguageMap.lean` and validate it with only a small
   number of downstream migrations.

3. Cleanup of instances in `Semantics`, `Types`, and `Satisfiability`.
   The goal is to significantly reduce occurrences of `letI := constantsOn.structure ...`.

4. Reorganization of subset-based wrappers.
   Make the `A : Set M` path explicitly a special case of the general parameter interface.

5. Optional `univ` / complete-type transport layer.

## Migration and Validation Checklist

Each phase should check at least the following:

- `Mathlib/ModelTheory/LanguageMap.lean` introduces no new instance loops
- the relevant proofs in `Mathlib/ModelTheory/Syntax.lean` and
  `Mathlib/ModelTheory/Semantics.lean` do not become worse because of simp-direction changes
- `Mathlib/ModelTheory/Definability.lean`, `Types.lean`, and `Satisfiability.lean` still admit
  short proofs of the original results
- the wrappers around `withConstants` in `Substructures.lean` and `ElementaryMaps.lean` do not
  become more awkward
- new names remain consistent with existing naming patterns around
  `sumMap`, `sumElim`, and `lhomWithConstantsMap`
- valuation-driven local uses of `constantsOn.structure` decrease substantially, without forcing
  genuinely generic expanded-language APIs into valuation-only form
- reduct-side issues are not accidentally entangled with the valuation-driven refactor unless they
  simplify as a byproduct

## End State

After the refactor, `LanguageMap.lean` should satisfy the following:

- it gives a complete and compositional description of the relationships among language maps,
  sums, constant expansions, and parameter reindexing
- it has a canonical carrier-level packaging for constant interpretations over arbitrary parameter
  types
- subset-based usage remains simple, but no longer dictates the underlying design
- downstream modules no longer need local instance tricks to manufacture constant-expansion
  structures on demand
- valuation-driven semantic entry points are clean, while genuinely generic expanded-language APIs
  remain available and conceptually separate
- the patch-style API currently living in the reference repository can be upstreamed naturally
  rather than maintained as a long-term fork
