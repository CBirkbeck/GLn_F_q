import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Tactic.Have
import Mathlib.Data.Matrix.Rank

open Matrix BigOperators

variable (n : ℕ) {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]

local notation "q" => Fintype.card 𝔽

noncomputable instance {k : ℕ} :
    Fintype ({ s : Fin k → (Fin n → 𝔽) // LinearIndependent 𝔽 s}) :=
  Fintype.ofFinite _

noncomputable instance {s : { s : Fin k → Fin n → 𝔽 // LinearIndependent 𝔽 s }} :
    Fintype (Submodule.span 𝔽 (Set.range (s : Fin k → Fin n → 𝔽)) : Set (Fin n → 𝔽)) :=
  Fintype.ofFinite _

noncomputable instance {s : { s : Fin k → Fin n → 𝔽 // LinearIndependent 𝔽 s }} :
    Fintype ((Submodule.span 𝔽 (Set.range (s : Fin k → Fin n → 𝔽)))ᶜ : Set (Fin n → 𝔽)) :=
  Fintype.ofFinite _

lemma complement_card (s : { s : Fin k → Fin n → 𝔽 // LinearIndependent 𝔽 s }):
    Fintype.card ((Submodule.span 𝔽 (Set.range (s : Fin k → Fin n → 𝔽)))ᶜ : Set (Fin n → 𝔽)) =
      (q) ^ n - (q) ^ k := by
  rw [Fintype.card_compl_set, Fintype.card_fun, Fintype.card_fin]
  simp only [SetLike.coe_sort_coe]
  rw [card_eq_pow_finrank (K := 𝔽) (V := Submodule.span 𝔽 (Set.range (s : Fin k → Fin n → 𝔽))),
    finrank_span_eq_card s.property, Fintype.card_fin]

def inductiveStepEquiv (k : ℕ) :
    { s : Fin (k + 1) → Fin n → 𝔽 // LinearIndependent 𝔽 s } ≃
      Σ s : { s : Fin k → Fin n → 𝔽 // LinearIndependent 𝔽 s },
        ((Submodule.span 𝔽 (Set.range (s : Fin k → Fin n → 𝔽)))ᶜ : Set (Fin n → 𝔽)) where
  toFun s := by
    have := linearIndependent_fin_succ.mp s.property
    use ⟨Fin.tail s.val, this.left⟩
    exact ⟨s.val 0, this.right⟩
  invFun s := by
    use Fin.cons s.2.val s.1.val
    exact linearIndependent_fin_cons.mpr ⟨s.1.property, s.2.property⟩
  left_inv _ := by simp only [Fin.cons_self_tail, Subtype.coe_eta]
  right_inv := fun ⟨_, _⟩ => by simp only [Fin.cons_zero, Subtype.coe_eta, Sigma.mk.inj_iff,
    Fin.tail_cons, heq_eq_eq, and_self]

lemma inductive_step_card (k : ℕ) :
    Fintype.card { s : Fin (k + 1) → Fin n → 𝔽 // LinearIndependent 𝔽 s } =
      Fintype.card { s : Fin k → Fin n → 𝔽 // LinearIndependent 𝔽 s } *
      ((q) ^ n - (q) ^k) := by
  rw [Fintype.card_congr (inductiveStepEquiv n k), Fintype.card_sigma]
  simp only [complement_card n, Finset.sum_const]
  rfl

lemma step2 {k : ℕ} (hk : k ≤ n) :
    Fintype.card { s : Fin k → (Fin n → 𝔽) // LinearIndependent 𝔽 s } =
      ∏ i : Fin k, ((q) ^ n - (q) ^ i.val) := by
  induction' k with k ih
  · simp only [Nat.zero_eq, LinearIndependent, Finsupp.total_fin_zero, LinearMap.ker_zero,
    Fintype.card_ofSubsingleton, Finset.univ_eq_empty, Finset.prod_empty]
  · simp only [inductive_step_card n k, ih (Nat.le_of_succ_le hk), mul_comm,
    Fin.prod_univ_succAbove _ k, Fin.natCast_eq_last, Fin.val_last, Fin.succAbove_last,
    Fin.coe_castSucc]

lemma eq_matrix_basis (M : Matrix (Fin n) (Fin n) 𝔽) : M = Basis.toMatrix (Pi.basisFun 𝔽 (Fin n)) (Matrix.transpose M) := by
  ext
  rw [Basis.toMatrix, Pi.basisFun_repr, transpose_apply]

noncomputable def equiv_GL_linearindependent (hn : 0 < n) :
    GL (Fin n) 𝔽 ≃ { s : Fin n → (Fin n → 𝔽) // LinearIndependent 𝔽 s } where
  toFun M := ⟨Matrix.transpose M, by
    apply linearIndependent_iff_card_eq_finrank_span.2
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_cols, Matrix.rank_unit]⟩
  invFun M := by
    apply Matrix.GeneralLinearGroup.mk'' (Matrix.transpose ( M.1 : Matrix (Fin n) (Fin n) 𝔽))
    rw [eq_matrix_basis n (Matrix.transpose (M.1)), transpose_transpose]
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hn
    have hdim : Fintype.card (Fin n) = FiniteDimensional.finrank 𝔽 (Fin n → 𝔽) := by
      simp only [Fintype.card_fin, FiniteDimensional.finrank_fintype_fun_eq_card]
    let b := basisOfLinearIndependentOfCardEqFinrank M.2 hdim
    rw [show M = ⇑b by simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]]
    have : Invertible ((Pi.basisFun 𝔽 (Fin n)).toMatrix ⇑b) := (Pi.basisFun 𝔽 (Fin n)).invertibleToMatrix b
    exact Matrix.isUnit_det_of_invertible _
  left_inv := by
    intro
    ext
    simp only [transpose_transpose]
    exact rfl
  right_inv := by exact congrFun rfl

noncomputable instance fintype : Fintype (GL (Fin n) 𝔽) := by
    exact Fintype.ofFinite (GL (Fin n) 𝔽)

lemma card_GL : Fintype.card (GL (Fin n) 𝔽) =
        ∏ i : (Fin n), (q ^ (n) - q ^ ( i : ℕ )) := by
    by_cases hn : n = 0
    · rw [hn]
      simp only [Fintype.card_unique, Finset.univ_eq_empty, mul_zero, pow_zero,
      Finset.prod_empty]
    · rw [Fintype.card_congr (equiv_GL_linearindependent n (Nat.pos_of_ne_zero hn))]
      exact step2 _ (Nat.le_refl n)
