module

public import Mathlib.ModelTheory.ElementarySubstructures
public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.PartialEquiv
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
- `FirstOrder.Language.Theory.isExistentiallyClosed_of_isExtensionPair`

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
  intro n φ hφ v hv
  simpa using hv

/-- Composition of existential embeddings is existential. -/
theorem IsExistential.comp {f : M ↪[L] N} {g : N ↪[L] P} :
    f.IsExistential → g.IsExistential → (g.comp f).IsExistential := by
  intro h h₁ α φ hφ v hφ'
  exact h hφ v <| h₁ hφ (f ∘ v) <| by simpa using hφ'

/-- An elementary embedding is existential. -/
theorem isExistential_of_elementary (f : M ↪ₑ[L] N) : f.toEmbedding.IsExistential := by
  intro α φ hφ v hv
  simpa using hv

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
      simp only [BoundedFormula.realize_exs]
      exact ⟨xs, hφ'⟩
    simpa [BoundedFormula.realize_exs] using h hφ.isExistential.exs v hφ'
  · exact f.isExistential_of_exists

lemma imap_exBoundedFormula {f : M ↪[L] N}
    (h : f.IsExistential) :
    ∀ {α : Type*} (n : ℕ) (φ : L.BoundedFormula α n)
      (_hφ : φ.IsExistential) (v : α → M),
      (∃ xs : Fin n → N, φ.Realize (f ∘ v) xs) ↔
        ∃ ys : Fin n → M, φ.Realize v ys := by
  classical
  have hfin := f.isExistential_boundedFormula_fin_of_exists ((isExistential_iff_exists f).1 h)
  intro α n φ hφ v
  constructor
  · rintro ⟨xs, hφ'⟩
    let s := φ.freeVarFinset
    let e := Fintype.equivFin s
    let ψ := BoundedFormula.relabelEquiv e (φ.restrictFreeVar id)
    have hψ : ψ.IsExistential := by
      simpa only [BoundedFormula.freeVarFinset, BoundedFormula.freeVarFinset.eq_5, ψ] using
        (hφ.restrictFreeVar id).relabelEquiv e
    have hφ'' : ψ.Realize (f ∘ (v ∘ Subtype.val ∘ e.symm)) xs := by
      simp [ψ, BoundedFormula.realize_relabelEquiv]
      simpa [Function.comp_assoc] using
        (BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
          (v := f ∘ v ∘ Subtype.val) (v' := f ∘ v) (xs := xs) (by simp)).2 hφ'
    obtain ⟨ys, hys⟩ := hfin (Fintype.card ↥s) n ψ hψ (v ∘ Subtype.val ∘ e.symm) xs hφ''
    exact ⟨ys, by simpa [ψ, BoundedFormula.realize_restrictFreeVar] using hys⟩
  · rintro ⟨ys, hys⟩
    exact ⟨f ∘ ys, hφ.realize_embedding f hys⟩

lemma map_exFormula (f : M ↪[L] N) {h : f.IsExistential}
    {α : Type*} (φ : L.Formula α) (hφ : φ.IsExistential) (v : α → M) :
    φ.Realize (f ∘ v) ↔ φ.Realize v := by
  simpa [Formula.Realize] using f.imap_exBoundedFormula h 0 φ hφ v

end Embedding

namespace Equiv

/-- A first-order equivalence induces an existential embedding. -/
theorem isExistential (f : M ≃[L] N) : f.toEmbedding.IsExistential := by
  intro α φ hφ v hv
  simpa using hv

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

/-- If every model of `T` forms an extension pair with `M`, then `M` is existentially closed. -/
theorem isExistentiallyClosed_of_isExtensionPair (T : L.Theory) (M : Type w)
    [L.Structure M] [M ⊨ T]
    (hExt : ∀ N : Theory.ModelType.{u, v, max u v w} T, L.IsExtensionPair N M) :
    T.IsExistentiallyClosed M := by
  classical
  dsimp [IsExistentiallyClosed]
  intro N f
  refine f.isExistential_of_exists ?_
  intro m n φ hφ x xs hxs
  have hmain :
      ∀ ws : Finset N,
        ∃ S : L.Substructure N,
          ∃ xS : Fin m → S,
            S.FG ∧ ((ws : Set N) ⊆ S) ∧
              (Substructure.subtype S ∘ xS = f ∘ x) ∧
              ∃ g : S ↪[L] M, g ∘ xS = x := by
    intro ws
    refine Finset.induction_on ws ?_ ?_
    · let S : L.Substructure N := Substructure.closure L (Set.range (f ∘ x))
      let xS : Fin m → S := fun i =>
        ⟨f (x i), Substructure.subset_closure (L := L) ⟨i, rfl⟩⟩
      have hS_le_range : S ≤ f.toHom.range := by
        refine Substructure.closure_le.2 ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨x i, rfl⟩
      refine ⟨S, xS, Substructure.fg_closure (Set.finite_range _), by simp, by
        funext i
        rfl, f.equivRange.symm.toEmbedding.comp (Substructure.inclusion hS_le_range), by
        funext i
        change f.equivRange.symm (f.equivRange (x i)) = x i
        exact Equiv.symm_apply_apply f.equivRange (x i)⟩
    · intro a ws _ ih
      obtain ⟨S, xS, hS_fg, hS_ws, hxS, g, hg⟩ := ih
      obtain ⟨g', hg'⟩ :=
        (isExtensionPair_iff_exists_embedding_closure_singleton_sup).1 (hExt N) S hS_fg g a
      let S' : L.Substructure N := Substructure.closure L (Set.singleton a) ⊔ S
      let xS' : Fin m → S' := fun i => (Substructure.inclusion le_sup_right) (xS i)
      refine ⟨S', xS', (Substructure.fg_closure_singleton _).sup hS_fg, ?_, ?_, g', ?_⟩
      · change ∀ y, y ∈ insert a ws → y ∈ S'
        intro y hy
        rcases Finset.mem_insert.1 hy with hEq | hy
        · have ha : a ∈ Substructure.closure L (Set.singleton a) :=
            Substructure.subset_closure (L := L) (Set.mem_singleton a)
          have hleft : Substructure.closure L (Set.singleton a) ≤ S' := by
            dsimp [S']
            exact le_sup_left
          subst y
          exact hleft ha
        · have hright : S ≤ S' := by
            dsimp [S']
            exact le_sup_right
          exact hright (hS_ws hy)
      · funext i
        change ((xS' i : _)) = f (x i)
        simpa [xS'] using congr_fun hxS i
      · funext i
        have hEq := (Embedding.ext_iff.1 hg') (xS i)
        exact hEq.symm.trans (congr_fun hg i)
  obtain ⟨S, xS, _, hS_ws, hxS, g, hg⟩ := hmain (Finset.univ.image xs)
  let xsS : Fin n → S := fun i => ⟨xs i, hS_ws (Finset.mem_image.2 ⟨i, by simp⟩)⟩
  refine ⟨g ∘ xsS, ?_⟩
  simpa [hg] using
    (hφ.realize_embedding g (v := xS) (xs := xsS)).2 <|
      (hφ.realize_embedding (Substructure.subtype S) (v := xS) (xs := xsS)).1 <| by
        rw [hxS]
        simpa [xsS] using hxs

end Theory

end Language

end FirstOrder
