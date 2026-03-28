# Stability theory in Mathlib — interface checklist

This file is a local scratch checklist of interfaces that are still missing or currently too thin in
`Mathlib/ModelTheory` for an ergonomic development of classical first-order stability theory.
It is ordered roughly by dependency, not by historical importance. It is not an implementation plan.

## Scope and conventions

- Primary context: a complete first-order theory `T : L.Theory`, usually inside a fixed sufficiently
  saturated and strongly homogeneous monster model `C ⊨ T`.
- Variables should work both for arbitrary index types `α` and for common finite-tuple forms such
  as `Fin n`.
- The library should support three interchangeable presentations of "formulas over parameters":
  - `L[[A]].Formula α`
  - `L.Formula (A ⊕ α)`
  - definable / type-definable subsets of assignments `α → M`
- Restriction to smaller parameter sets and transport along embeddings / language maps should be
  explicit library interfaces, not just ad hoc rewrites.

## Baseline already available

- `T.IsComplete`, complete theories, and complete theories of models.
- `T.CompleteType α` as maximal consistent theories in `L[[α]]`.
- Basic topology on `CompleteType`, with clopen basic opens; `TotallySeparatedSpace`, hence
  `T2Space`.
- Definable sets with parameters.
- Elementary embeddings, elementary substructures, and downward Lowenheim-Skolem.
- Ultraproducts and Fraisse-side ultrahomogeneity infrastructure.

## Layer 1: parameter syntax and tuple bookkeeping

- A stable API for splitting variables into object variables and parameter variables:
  `x`, `y`, `x ⊕ y`, `Fin m ⊕ Fin n`, etc.
- Explicit equivalences and simp lemmas between `L[[A]].Formula x` and `L.Formula (A ⊕ x)`.
- Reindexing / relabeling / substitution interfaces for formulas and types that are usable without
  unfolding syntax definitions.
- Transport of formulas along parameter maps `A → B`, inclusions `A ⊆ B`, elementary embeddings,
  and language morphisms.
- Tuple projection / concatenation / permutation APIs for `α → M`, enough to state formulas
  `φ(x; y)` cleanly.

## Layer 2: partial types and type-definable objects

- A definition of partial type over parameters `A` in variables `x`.
- Predicates and API for consistency, finite satisfiability, realizability in a model, and
  equivalence of partial types.
- A `Realizes` predicate: `Realizes M p a`.
- Completion API: extend a consistent partial type to a complete type.
- Restriction of a complete type to its underlying partial type.
- Type-definable sets as intersections of definable sets / sets cut out by partial types.
- Closed subsets of type spaces corresponding to partial types.

## Layer 3: parameterized complete types `S_x(A)`

- A first-class interface for complete types over a parameter set / substructure / model, not only
  over the bare theory `T`.
- Restriction maps `S_x(B) → S_x(A)` for `A ⊆ B`.
- Extension interfaces and existence lemmas.
- Pushforward / pullback along inclusions, elementary embeddings, isomorphisms, and language maps.
- "Realized in `M`" predicates and API for realized types over `A`.
- Orbit characterizations of types over parameters when working in a saturated / homogeneous
  context.

## Layer 4: formula equivalence and Stone duality

- Quotient `L.Formula x` modulo semantic equivalence over `T` or over `A`.
- Boolean algebra structure on that quotient.
- The clopen subset attached to a formula as a map from the quotient Boolean algebra to
  `Set (S_x(A))`.
- Ultrafilter / Stone duality description of complete types.
- API showing that complete types are exactly Boolean algebra homomorphisms / ultrafilters, as
  needed.

## Layer 5: topology on type spaces

- `CompactSpace` results for Stone spaces `S_x(T)` and `S_x(A)`.
- Compactness lemmas in topological form, usable in indiscernible and stability arguments.
- Continuity of restriction maps, relabeling maps, transport maps induced by elementary embeddings,
  and language morphisms.
- A clopen basis API that supports finite intersections, complements, preimages, and basis
  membership without unfolding `generateFrom`.
- The correspondence:
  - formulas ↔ clopen subsets
  - partial types ↔ closed subsets

## Layer 6: cardinality and size control

- Cardinality bounds for the set of formulas over parameters `A`.
- Cardinality bounds and monotonicity for `S_x(A)`.
- "Small parameter set" / "`< κ`-sized" interfaces compatible with monster-model arguments.
- Set-theoretic lemmas connecting Lowenheim-Skolem, saturation, and type-counting definitions.
- Enough size bookkeeping to state `κ`-stability cleanly.

## Layer 7: saturation, homogeneity, and monster-model scaffolding

- Definitions of `κ`-saturation, `κ`-homogeneity, and strong homogeneity.
- Transfer lemmas between saturation notions for tuples / parameter sets.
- Existence results or wrappers providing "enough saturation" for downstream arguments.
- A `MonsterModel` wrapper / structure / typeclass carrying:
  - a complete theory `T`
  - a distinguished model `C ⊨ T`
  - saturation / homogeneity hypotheses
  - a notion of small parameter set
- Basic extension and back-and-forth lemmas over small parameter sets.

## Layer 8: automorphisms and invariance

- `Aut(M)` as a group of structure automorphisms.
- `Aut(M/A)` as the subgroup fixing `A` pointwise.
- Actions of automorphism groups on tuples, definable sets, partial types, and complete types.
- Orbit ↔ type correspondences over `A`.
- Invariant sets / invariant partial types / invariant complete types.
- API for transporting realizations and types by automorphisms.

## Layer 9: indiscernibles and EM interfaces

- Definitions of indiscernible sequences over a parameter set `A`.
- Order-indiscernibles for linear orders as the primary interface.
- Basic closure properties: subsequences, reindexing by order isomorphism, concatenation when
  valid.
- Extraction / existence interfaces from compactness / Ramsey-style arguments.
- EM-types or a thinner replacement sufficient to produce indiscernibles.
- Morley sequences once nonforking exists.

## Layer 10: closure operators and algebraicity

- Algebraic formulas / finite solution-set APIs over parameter sets.
- Algebraic closure `acl(A)` and definable closure `dcl(A)`.
- Basic closure-operator lemmas: monotonicity, idempotence, finite character, transport under
  embeddings / automorphisms.
- Orbit-based characterizations of `acl` and `dcl` in saturated contexts.
- Interaction with parameterized types and isolated / principal types.

## Layer 11: dividing, forking, heirs, coheirs

- Definitions of dividing and forking over parameter sets.
- Nondividing / nonforking extension.
- Heir, coheir, and invariant extension interfaces.
- Basic calculus: invariance, monotonicity, base monotonicity, transitivity, symmetry, extension,
  existence.
- Finite satisfiability and definability characterizations where appropriate.
- Morley-sequence API over nonforking extensions.

## Layer 12: core stability notions

- Stable formula and stable theory.
- Order property / independence property style witness interfaces as needed.
- Basic equivalences between stability formulations.
- Type-counting definitions of `κ`-stability and monotonicity facts.
- Definability of types in stable theories.
- Stationarity and uniqueness of nonforking extensions in stable theories.
- Local character results in the stable context.

## Layer 13: imaginaries and canonical parameters

- Definable equivalence relations and quotient-sort interfaces.
- Imaginary sorts / `eq`-expansion infrastructure.
- Elimination of imaginaries API where available.
- Strong types, Lascar strong types, and bounded-invariant equivalence relations.
- Canonical parameters / canonical bases for definable sets and stationary types.

## Layer 14: optional but standard advanced layers

- Isolated / principal types.
- Prime and atomic models over sets or models.
- Rank notions: Morley rank / degree, `U`-rank, Lascar rank.
- Orthogonality, regular types, nonmultidimensionality, decomposition-style infrastructure.
- Stability spectrum statements beyond the basic definitions.

## Adjacent non-stability infrastructure that still matters

- Better category / transport structure on bundled structures and models.
- More complete Skolemization interfaces.
- More ergonomic APIs around elementary chains, unions of chains, and directed limits.
- Library support for switching between syntax, semantics, and bundled-model viewpoints.

## Notes on current gaps vs existing library

- `T2Space` / Hausdorff for `CompleteType` is already effectively present via
  `TotallySeparatedSpace`; compactness is the missing topological headline.
- `CompleteType` exists, but the parameterized `S_x(A)` / partial-type / type-definable layer is
  still the main missing foundation.
- The current TODOs in `Types.lean`, `Equivalence.lean`, `Bundled.lean`, and `Skolem.lean` remain
  relevant inputs to this checklist.
