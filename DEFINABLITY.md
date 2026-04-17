# Notes on Possible API Gaps in `Mathlib/ModelTheory/Definability.lean`

This document records possible additions to the API of
`Mathlib/ModelTheory/Definability.lean`, with an emphasis on basic definable sets,
definable functions, and lemmas that are useful for automation.

## Current Situation

The file already has strong closure properties at the foundational level:

- Boolean operations on definable sets.
- Finite intersections and unions.
- Finite projections via `Definable.image_comp`.
- Finite existential and universal quantification.
- Basic unary and binary shapes through `Definable.singleton` and `Definable.diagonal`.
- Graph-based definitions of `DefinableFun` and coordinatewise definitions of `DefinableMap`.
- A generic substitution lemma `Set.Definable.preimage_map`.
- Useful equality corollaries such as `DefinableFun.setOf_eq` and
  `DefinableFun.setOf_eq_const`.

The main weakness is not the lack of foundational closure. The gap is mostly at the user-facing
API level: there are only a few specialized lemmas for common patterns, so downstream proofs often
have to drop to lower-level encodings.

Several structural gaps seem especially relevant.

- There is no obvious syntax-to-definability bridge for `Formula` or `BoundedFormula`, so proofs
  still reconstruct `Set.empty_definable_iff` by hand.
- There is also no obvious bridge specialized to `Definable₁` and `Definable₂`, even though these
  are the most common downstream entry points.
- The `DefinableMap` API is missing basic constructors and combinators. Many concrete set-shape
  lemmas should really be corollaries of those lower-level map lemmas rather than added first.
- The API is asymmetric across `Definable`, `DefinableFun`, and `TermDefinable`: for example,
  `Definable.map_expansion` and `TermDefinable.map_expansion` exist, but there is no corresponding
  `DefinableFun.map_expansion` or `DefinableMap.map_expansion`.

## Corrections to the Original Gap List

A few items in the earlier draft should be reclassified.

- `DefinableFun.setOf_eq` and `DefinableFun.setOf_eq_const` already exist, so they should not be
  listed as missing corollaries.
- `Set.Definable.preimage_map` already supplies the core generic substitution mechanism. The real
  missing layer is a convenient front end, together with enough `DefinableMap` constructors to
  make that front end easy to use.
- A theorem named `Formula.definable` should probably be parameter-free:

```lean
theorem Formula.definable (φ : L.Formula α) :
    (∅ : Set M).Definable L (setOf φ.Realize)
```

If one wants a parameterized statement over `A`, it is more natural to phrase it for
`L[[A]].Formula α` and return `A.Definable L _`.

## 1. Bridges and Basic Shapes on the Set Side

### Bridge from syntax to `Set.Definable`

The most basic missing bridge seems to be:

```lean
theorem Formula.definable (φ : L.Formula α) :
    (∅ : Set M).Definable L (setOf φ.Realize)
```

This is not mathematically deep, but it would remove a large amount of repeated boilerplate based
on `Set.empty_definable_iff`.

If a parameterized version is wanted, a separate theorem for formulas in `L[[A]]` would likely be
cleaner than overloading the parameter-free statement.

For bounded formulas, two wrappers seem natural:

```lean
theorem BoundedFormula.definable (φ : L.BoundedFormula α n) :
    (∅ : Set M).Definable L {v : α ⊕ Fin n → M | φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)}

theorem BoundedFormula.definable_empty (φ : L.BoundedFormula Empty n) :
    (∅ : Set M).Definable L {xs : Fin n → M | φ.Realize default xs}
```

The first is the canonical bridge, phrased on the full free-plus-bound variable space. The second
is the important `Empty` specialization, which occurs frequently in model-theoretic proofs.

These lemmas should likely be regarded as thin wrappers over `Formula.definable` together with the
existing semantic bridge `BoundedFormula.realize_toFormula`.

### Bridges specialized to `Definable₁` and `Definable₂`

The generic bridges above are not quite enough for ergonomic downstream use. In practice, many
proofs target `Definable₁` or `Definable₂` directly, so it would be useful to add thin wrappers
specialized to those abbreviations.

Possible examples:

```lean
theorem Formula.definable₁ (φ : L.Formula (Fin 1)) :
    (∅ : Set M).Definable₁ L {x : M | φ.Realize ![x]}

theorem BoundedFormula.definable₁ (φ : L.BoundedFormula Empty 1) :
    (∅ : Set M).Definable₁ L {x : M | φ.Realize default ![x]}
```

The exact statements can be tuned, but the main point is to avoid forcing every downstream file to
open up `Definable₁`, rewrite tuples by hand, and rebuild the formula witness manually.

### Existing reindex API on definable sets

Before adding more set-side wrappers, it is worth recording that `Set.Definable` already has
useful reindex operations:

- `Definable.preimage_comp`
- `Definable.image_comp_equiv`
- `Definable.image_comp`

So the main set-side gap is probably not another generic reindex theorem. The more important gap is
bridging syntax to definability and then combining definable sets with definable maps.

### Basic shapes of definable sets

The following concrete shapes would still likely be useful additions, but many of them should be
easy corollaries once the bridge lemmas and `DefinableMap` API are improved.

### Finite unary sets

The file currently provides singleton sets, but not the more usable closure API built from them.
Useful lemmas would include:

- definability of `insert`
- definability of unordered pairs
- definability of finite subsets of `M`

These would immediately give cofinite sets by complement.

### Coordinate hyperplanes and repeated-coordinate loci

Common model-theoretic shapes include:

- `{v | v i = v j}`
- `{v | v i = a}` for `a ∈ A`
- finite intersections of such conditions

These are basic coordinate equations and are often used as the smallest building blocks in proofs.

### Rectangles and cylinders

For unary definable sets `s t : Set M`, it is natural to want:

- definability of `s ×ˢ t`
- definability of `s ×ˢ Set.univ`
- definability of `Set.univ ×ˢ t`

These are basic binary shapes and are often easier to use than direct formula constructions.

### Fibers and sections of definable binary relations

If `R : Set (M × M)` is definable and `a ∈ A`, useful special cases are:

- `{x | (x, a) ∈ R}`
- `{y | (a, y) ∈ R}`

These are just sections of definable relations, but they appear constantly in practice.

### Graphs of unary definable functions

The file already contains `TermDefinable₁.definable₂_graph`, but there is no similarly direct
user-facing result for general `DefinableFun` in the unary case. That would be a natural addition.

### Term-definable points and singleton corollaries

There is also room for one-step corollaries that turn term-definable elements or unary
term-definable functions into the small definable sets that occur in model-theoretic arguments.

For example, after exposing `TermDefinable.definableFun`, it would be natural to add corollaries
showing:

- the singleton of a term-definable point is definable
- the graph of a unary term-definable map is definable without reopening the tuple-graph encoding

These would remove hand-written witnesses in downstream files such as
`Mathlib/ModelTheory/ElementarySubstructures.lean`.

## 2. Basic Lemmas About Definable Functions and Maps

The current API for `DefinableFun` is fairly small, and the API for `DefinableMap` is even
thinner. The following additions would likely have the highest value.

### Bridge from term-definable to definable

This looks like the most important missing bridge:

```lean
@[fun_prop] theorem TermDefinable.definableFun {f : (α → M) → M}
    (hf : A.TermDefinable L f) : A.DefinableFun L f
```

The file already proves that a term-definable function has a definable tuple graph. Exposing the
result directly as `DefinableFun` would make the API much smoother and would improve automation.

### Basic constructors for `DefinableMap`

The most urgent missing API seems to be the basic finite-product structure of `DefinableMap`.
Natural primitives include:

```lean
@[fun_prop] theorem DefinableMap.reindex {f : β → α}
    (hF : A.DefinableMap L F) :
    A.DefinableMap L (fun x => F x ∘ f)

@[fun_prop] theorem DefinableMap.const
    (h : ∀ i, g i ∈ A) :
    A.DefinableMap L (fun _ : α → M => g)

@[fun_prop] theorem DefinableMap.sumElim
    (hF : A.DefinableMap L F) (hG : A.DefinableMap L G) :
    A.DefinableMap L (fun x => Sum.elim (F x) (G x))
```

Depending on the preferred indexing conventions, this could also be packaged as `append`, `prod`,
or a `vars` lemma. The key point is that `Fin.snoc`, `Fin.cons`, and similar tuple-building maps
should be derived consequences of these primitives rather than proved ad hoc in downstream files.

In practice, the plan should explicitly include the tuple-building corollaries, not just the
abstract primitives. A particularly useful batch would be:

- `DefinableMap.pair`
- `DefinableMap.cons`
- `DefinableMap.snoc`
- vector constructors such as `fun v => ![f v, g v]`

These are the forms that appear in actual downstream proofs.

### Identity, monotonicity, and composition for definable maps

Natural automation-friendly lemmas include:

```lean
@[fun_prop] theorem DefinableMap.id :
    A.DefinableMap L (fun x : α → M => x)

@[fun_prop] theorem DefinableMap.comp [Finite β]
    {F : (α → M) → (β → M)} {G : (β → M) → (γ → M)}
    (hF : A.DefinableMap L F) (hG : A.DefinableMap L G) :
    A.DefinableMap L (G ∘ F)

@[fun_prop, gcongr] theorem DefinableMap.mono
    (hF : A.DefinableMap L F) (hAB : A ⊆ B) :
    B.DefinableMap L F
```

There is already a theorem `DefinableFun.comp`, so a new theorem named `DefinableFun.comp_map`
would mainly be an ergonomic alias or naming cleanup rather than a genuinely new capability.
By contrast, `DefinableMap.comp` and `DefinableMap.mono` still look like real gaps.

### Expansion lemmas for `DefinableFun` and `DefinableMap`

The file already has `Definable.map_expansion` and `TermDefinable.map_expansion`, so the natural
API-completion move is to add the corresponding statements for graph-definable functions and maps.

Possible statements are:

```lean
theorem DefinableFun.map_expansion (hf : A.DefinableFun L f)
    (φ : L →ᴸ L') [φ.IsExpansionOn M] : A.DefinableFun L' f

theorem DefinableMap.map_expansion (hF : A.DefinableMap L F)
    (φ : L →ᴸ L') [φ.IsExpansionOn M] : A.DefinableMap L' F
```

These are not deep, but they make the three parallel notions feel much more coherent.

## 3. Set Shapes That Should Follow from Basic Definable Functions and Sets

The key observation is that `Set.Definable.preimage_map` is already strong enough to express a
large amount of routine definability. What seems missing is a convenient specialized interface.

### Membership in a definable set after substitution

The most useful general schema would be a lemma of the form:

```lean
lemma Set.Definable.of_definableFun [Finite β]
    {S : Set (β → M)} (hS : A.Definable L S)
    {f : β → (α → M) → M} (hf : ∀ i, A.DefinableFun L (f i)) :
    A.Definable L {v | (fun i => f i v) ∈ S}
```

Conceptually, this says that a definable relation stays definable after plugging in definable
functions coordinatewise.

This single lemma would subsume or streamline many common special cases. It should probably be
developed only after the basic `DefinableMap` constructors and combinators are in place, since it
is really a specialized interface to `Set.Definable.preimage_map`.

### Immediate useful corollaries

Once that schema is available, the following become easy corollaries:

- `DefinableFun.setOf_mem` for unary target sets
- binary relation pullback lemmas such as `{v | (f v, g v) ∈ R}`
- finite conjunctions of equations between definable functions
- finite conjunctions of relation instances involving definable functions

The first two equality corollaries already exist in the file, so the plan should focus on the
genuinely missing variants such as `setOf_mem` and relation pullbacks.

In practice, this specialized front end is still one of the main missing ergonomic layers.

## 4. Bundled `DefinableSet`

The file already defines `L.DefinableSet A α` and equips it with a Boolean algebra structure.
However, the current plan does not say whether that bundled layer should remain minimal or be
expanded into a real user-facing API.

Two directions seem reasonable:

- keep it deliberately light and treat it as a packaging device around `Set.Definable`
- add bundled analogues of the most useful operations, such as reindexing and quantifier-like
  constructions, so users can stay inside the bundled world longer

Even if no expansion is planned, the document should record that this is an explicit design choice
rather than an accidental omission.

## 5. Automation and Maintenance

The plan should also mention small but high-value maintenance work that improves usability without
changing the mathematics.

### Automation attributes

Some natural compositional lemmas should probably carry `@[fun_prop]` or related automation
attributes whenever they are added. The goal is not just to have the theorems available, but to
make them discoverable by the automation already imported in this file.

### Sectioning and documentation

`Definability.lean` is now large enough that additional sectioning comments and a few docstrings on
the main bridge lemmas would likely pay for themselves. This is especially true if the API grows
further around `DefinableMap`, substitution, and syntax bridges.

## 6. Suggested First Batch of Additions

If only a small first batch should be added, the following seem the most valuable.

1. `Formula.definable` and `BoundedFormula.definable`, together with at least one ergonomic
   `Definable₁`-specialized wrapper
2. `TermDefinable.definableFun`
3. basic `DefinableMap` constructors such as `reindex`, `const`, and `sumElim` or `append`
4. tuple-building corollaries such as `pair`, `cons`, `snoc`, and vector constructors
5. `DefinableMap.id`, `DefinableMap.comp`, and `DefinableMap.mono`
6. `DefinableFun.map_expansion` and `DefinableMap.map_expansion`
7. specialized front-end lemmas for `Set.Definable.preimage_map`, especially `DefinableFun.setOf_mem`
   and relation pullbacks
8. concrete corollaries such as finite unary sets, sections of definable relations, and rectangle
   or cylinder lemmas for `Definable₂`

## Summary

The foundational theory in `Definability.lean` already looks strong. The main opportunity is to
add a better user-facing API:

- bridges from `Formula` and `BoundedFormula` to `Set.Definable`
- wrappers specialized to `Definable₁` and `Definable₂`
- better bridges from `TermDefinable` to `DefinableFun`
- basic constructors, tuple-building lemmas, and composition lemmas for `DefinableMap`
- specialized front ends for `Set.Definable.preimage_map`
- API symmetry across `Definable`, `DefinableFun`, and `TermDefinable`
- an explicit decision about how much bundled `DefinableSet` API should exist
- then more concrete shapes of definable sets as corollaries

These additions would mostly reduce proof overhead rather than enlarge the mathematical scope of
the file.
