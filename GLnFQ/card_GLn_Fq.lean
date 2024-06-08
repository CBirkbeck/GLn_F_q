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

lemma card_LinearInependent_subtype {k : ℕ} (hk : k ≤ n) :
    Fintype.card { s : Fin k → (Fin n → 𝔽) // LinearIndependent 𝔽 s } =
      ∏ i : Fin k, ((q) ^ n - (q) ^ i.val) := by
  induction' k with k ih
  · simp only [Nat.zero_eq, LinearIndependent, Finsupp.total_fin_zero, LinearMap.ker_zero,
    Fintype.card_ofSubsingleton, Finset.univ_eq_empty, Finset.prod_empty]
  · simp only [Fintype.card_congr (inductiveStepEquiv n k), Fintype.card_sigma, complement_card n, Finset.sum_const, Finset.card_univ, smul_eq_mul, ih (Nat.le_of_succ_le hk), mul_comm,
    Fin.prod_univ_succAbove _ k, Fin.natCast_eq_last, Fin.val_last, Fin.succAbove_last,
    Fin.coe_castSucc]

lemma eq_matrix_basis (M : Matrix (Fin n) (Fin n) 𝔽) :
    M = Basis.toMatrix (Pi.basisFun 𝔽 (Fin n)) (transpose M) := rfl

/-- Equivalence between `GL n F` and `n` vectors of length `n` that are linearly independent. Given
by sending a matrix to its coloumns. -/
noncomputable def equiv_GL_linearindependent {F : Type*} [Field F] (hn : 0 < n) :
    GL (Fin n) F ≃ { s : Fin n → (Fin n → F) // LinearIndependent F s } where
  toFun M := ⟨transpose M, by
    apply linearIndependent_iff_card_eq_finrank_span.2
    rw [Set.finrank, ← rank_eq_finrank_span_cols, rank_unit]⟩
  invFun M := by
    apply GeneralLinearGroup.mk'' (transpose (M.1))
    rw [eq_matrix_basis n (transpose (M.1)), transpose_transpose]
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hn
    have hdim : Fintype.card (Fin n) = FiniteDimensional.finrank F (Fin n → F) := by
      simp only [Fintype.card_fin, FiniteDimensional.finrank_fintype_fun_eq_card]
    let b := basisOfLinearIndependentOfCardEqFinrank M.2 hdim
    rw [show M = ⇑b by simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]]
    have : Invertible ((Pi.basisFun F (Fin n)).toMatrix ⇑b) :=
      (Pi.basisFun F (Fin n)).invertibleToMatrix b
    exact isUnit_det_of_invertible _
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
      exact card_LinearInependent_subtype _ (Nat.le_refl n)
