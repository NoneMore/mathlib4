module

public import Mathlib.ModelTheory.ElementarySubstructures
public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.Satisfiability

/-!
# Existentially Closed Models

## Main Definitions

- `FirstOrder.Language.Embedding.IsExistential`: an embedding which reflects existential formulas.
- `FirstOrder.Language.Theory.IsExistentiallyClosed`: a model in which every embedding into a
  model of the same theory is existential.

## Main Results

- `FirstOrder.Language.Embedding.isExistential_id`
- `FirstOrder.Language.Embedding.IsExistential.comp`
- `FirstOrder.Language.Embedding.isExistential_of_elementary`
- `FirstOrder.Language.Embedding.isExistential_of_exists`
- `FirstOrder.Language.Equiv.isExistential`

## Implementation notes

The lemmas `FirstOrder.Language.Embedding.isExistential_iff_exists` and
`FirstOrder.Language.Theory.isExistentiallyClosed_iff` are witness-style reformulations of the
definitions above. They are mainly intended as helper lemmas for working with quantifier-free
bounded formulas, rather than as separate mathematical criteria.
-/

@[expose] public section

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M N P : Type*}
variable [L.Structure M] [L.Structure N] [L.Structure P]

namespace Embedding

/-- An embedding is existential if it reflects existential formulas. -/
def IsExistential (f : M ↪[L] N) : Prop :=
  ∀ {n : ℕ} {φ : L.Formula (Fin n)}, φ.IsExistential →
    ∀ v : (Fin n) → M, φ.Realize (f ∘ v) → φ.Realize v

/-- The identity embedding is existential. -/
theorem isExistential_id : (Embedding.refl L M).IsExistential := by
  dsimp [IsExistential]
  aesop

/-- Composition of existential embeddings is existential. -/
theorem IsExistential.comp {f : M ↪[L] N} {g : N ↪[L] P} :
    f.IsExistential → g.IsExistential → (g.comp f).IsExistential := by
  dsimp [IsExistential]
  intro h h₁ α φ hφ v hφ'
  apply h
  · simp_all
  · apply h₁
    · simp_all
    · exact hφ'

/-- An elementary embedding is existential. -/
theorem isExistential_of_elementary (f : M ↪ₑ[L] N) : f.toEmbedding.IsExistential := by
  dsimp [IsExistential]
  intro α φ hφ v
  simp

lemma isExistential_boundedFormula_fin_of_exists (f : M ↪[L] N)
    (h :
      ∀ (m n : ℕ) (φ : L.BoundedFormula (Fin m) n)
        (_hφ : φ.IsQF) (x : Fin m → M) (xs : Fin n → N),
        φ.Realize (f ∘ x) xs →
          ∃ ys : Fin n → M, φ.Realize x ys) :
    ∀ (m n : ℕ) (φ : L.BoundedFormula (Fin m) n)
      (_hφ : φ.IsExistential) (x : Fin m → M) (xs : Fin n → N),
      φ.Realize (f ∘ x) xs →
        ∃ ys : Fin n → M, φ.Realize x ys := by
  intro m n φ hφ x xs hxs
  induction hφ with
  | of_isQF hQF => exact h _ _ _ hQF _ _ hxs
  | ex hφ ih =>
      simp only [BoundedFormula.realize_ex, Nat.succ_eq_add_one] at hxs ⊢
      obtain ⟨a, ha⟩ := hxs
      obtain ⟨ys, hys⟩ := ih (Fin.snoc xs a) ha
      exact ⟨Fin.init ys, ys (Fin.last _), by simpa [Fin.snoc_init_self] using hys⟩

/-- A finite-tuple witness condition for quantifier-free formulas implies that an embedding is
existential.
-/
theorem isExistential_of_exists (f : M ↪[L] N)
    (h :
      ∀ (m n : ℕ) (φ : L.BoundedFormula (Fin m) n)
        (_hφ : φ.IsQF) (x : Fin m → M) (xs : Fin n → N),
        φ.Realize (f ∘ x) xs →
          ∃ ys : Fin n → M, φ.Realize x ys) :
    f.IsExistential := by
  intro n φ hφ v hv
  obtain ⟨ys,hys⟩ := f.isExistential_boundedFormula_fin_of_exists h n 0 φ hφ v default hv
  simpa [Formula.Realize, Subsingleton.elim ys default] using hys

/-- Witness-style reformulation of `Embedding.IsExistential` using quantifier-free bounded
formulas and finite tuples of witnesses. -/
lemma isExistential_iff_exists (f : M ↪[L] N) :
    f.IsExistential ↔
      ∀ (m n : ℕ) (φ : L.BoundedFormula (Fin m) n)
        (_hφ : φ.IsQF) (x : Fin m → M) (xs : Fin n → N),
        φ.Realize (f ∘ x) xs →
          ∃ ys : Fin n → M, φ.Realize x ys := by
  constructor
  · intro h m n φ hφ v xs hφ'
    dsimp [Embedding.IsExistential] at h
    replace hφ' : (φ.exs).Realize (f ∘ v) := by
      simp only [BoundedFormula.realize_exs] ; exists xs
    have : φ.exs.Realize v := by
      exact h hφ.isExistential.exs v hφ'
    simpa using this
  · exact f.isExistential_of_exists

lemma imap_exBoundedFormula (f : M ↪[L] N)
    (h : f.IsExistential) :
    ∀ {α : Type*} (n : ℕ) (φ : L.BoundedFormula α n)
      (_hφ : φ.IsExistential) (v : α → M) (xs : Fin n → N),
      φ.Realize (f ∘ v) xs →
        ∃ ys : Fin n → M, φ.Realize v ys := by
  classical
  rw [isExistential_iff_exists] at h
  intro α n φ hφ v xs hφ'
  let s := φ.freeVarFinset
  let e := Fintype.equivFin s
  let ψ := BoundedFormula.relabelEquiv e (φ.restrictFreeVar id)
  replace hφ' : ψ.Realize (f ∘ (v ∘ Subtype.val ∘ e.symm)) xs := by
    simp [ψ, BoundedFormula.realize_relabelEquiv]
    simpa [Function.comp_assoc] using
      (BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
        (v := f ∘ v ∘ Subtype.val) (v' := f ∘ v) (xs := xs) (by simp)).2 hφ'
  induction hφ with
  | @of_isQF n' φ' hφ =>
    obtain ⟨ys,hys⟩ := h (Fintype.card ↥s) n' ψ (by
      simp only [ψ]
      exact (hφ.restrictFreeVar id).relabelEquiv e)
      (v ∘ Subtype.val ∘ ⇑e.symm) xs hφ'
    exists ys
    simpa [ψ, BoundedFormula.realize_restrictFreeVar] using hys
  | @ex n' φ' hφ h' =>
    apply isExistential_boundedFormula_fin_of_exists at h
    have : ψ.IsExistential := by
      simp only [BoundedFormula.freeVarFinset, BoundedFormula.freeVarFinset.eq_5, ψ]
      refine BoundedFormula.IsExistential.relabelEquiv ?_ e
      refine BoundedFormula.IsExistential.restrictFreeVar ?_ id
      exact BoundedFormula.IsExistential.ex hφ
    obtain ⟨ys,hys⟩ := h (Fintype.card ↥s) n' ψ this (v ∘ Subtype.val ∘ ⇑e.symm) xs hφ'
    exists ys
    simpa [ψ, BoundedFormula.realize_restrictFreeVar] using hys

end Embedding

namespace Equiv

/-- A first-order equivalence induces an existential embedding. -/
theorem isExistential (f : M ≃[L] N) : f.toEmbedding.IsExistential := by
  dsimp [Embedding.IsExistential]
  intro α φ hφ v
  simp

end Equiv

namespace Theory

variable {T : L.Theory}
variable {M : Type w} [L.Structure M] [M ⊨ T]

/-- A model of `T` is existentially closed if every embedding into another model of `T`
is existential. -/
def IsExistentiallyClosed (T : L.Theory) (M : Type w) [L.Structure M] [M ⊨ T] : Prop :=
  ∀ N : Theory.ModelType.{u, v, max u v w} T, ∀ f : M ↪[L] N, f.IsExistential

/-- Unfolding `Theory.IsExistentiallyClosed` through
`Embedding.isExistential_iff_exists`. -/
lemma isExistentiallyClosed_iff (T : L.Theory) (M : Type w) [L.Structure M] [M ⊨ T] :
    T.IsExistentiallyClosed M ↔
      ∀ N : Theory.ModelType.{u, v, max u v w} T,
        ∀ f : M ↪[L] N,
          ∀ (m n : ℕ) (φ : L.BoundedFormula (Fin m) n)
            (_hφ : φ.IsQF) (x : Fin m → M) (xs : Fin n → N),
            φ.Realize (f ∘ x) xs →
              ∃ ys : Fin n → M, φ.Realize x ys := by
  dsimp [IsExistentiallyClosed]
  simp [Embedding.isExistential_iff_exists]

end Theory

end Language

end FirstOrder
