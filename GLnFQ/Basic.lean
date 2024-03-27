import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Tactic.Have

open Matrix BigOperators

variable (p n : ℕ) [Fact (Nat.Prime p)] (m : ℕ+)

noncomputable instance fintype : Fintype (GL (Fin n) (GaloisField p m)) := by
    exact Fintype.ofFinite (GL (Fin n) (GaloisField p m))

lemma card : Fintype.card (GL (Fin n) (GaloisField p m)) =
        ∏ i : (Fin n), (p ^ (m * n) - p ^ (n * i)) := by
    induction' n with n ih
    simp only [Nat.zero_eq, Fintype.card_unique, Finset.univ_eq_empty, mul_zero, pow_zero, zero_mul,
      ge_iff_le, le_refl, tsub_eq_zero_of_le, Finset.prod_const, Finset.card_empty]


    sorry

local notation "𝔽" => (GaloisField p m)

variable (v : Fin n → 𝔽)





--Basis.invertibleToMatrix might be useful to turn it into a question about bases.


section Step2

variable {p n m}

noncomputable instance {k : ℕ} :
    Fintype ({ s : Fin k → (Fin n → 𝔽) // LinearIndependent 𝔽 s}) :=
  Fintype.ofFinite _

noncomputable instance {s : { s : Fin k → Fin n → 𝔽 // LinearIndependent 𝔽 s }} :
    Fintype (Submodule.span 𝔽 (Set.range (s : Fin k → Fin n → 𝔽)) : Set (Fin n → 𝔽)) :=
  Fintype.ofFinite _

noncomputable instance {s : { s : Fin k → Fin n → 𝔽 // LinearIndependent 𝔽 s }} :
    Fintype ((Submodule.span 𝔽 (Set.range (s : Fin k → Fin n → 𝔽)))ᶜ : Set (Fin n → 𝔽)) :=
  Fintype.ofFinite _

lemma complement_card  (s : { s : Fin k → Fin n → 𝔽 // LinearIndependent 𝔽 s }):
    Fintype.card ((Submodule.span 𝔽 (Set.range (s : Fin k → Fin n → 𝔽)))ᶜ : Set (Fin n → 𝔽)) =
      (p ^ (m : ℕ)) ^ n - (p ^ (m : ℕ)) ^ k := by
  rw [Fintype.card_compl_set, Fintype.card_fun, GaloisField.card _ _ , Fintype.card_fin]
  simp only [SetLike.coe_sort_coe]
  rw [card_eq_pow_finrank (K := 𝔽), finrank_span_eq_card s.property, GaloisField.card _ _ ,
    Fintype.card_fin]
  exact PNat.ne_zero m
  exact PNat.ne_zero m

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
  left_inv _ := by simp
  right_inv := fun ⟨_, _⟩ => by simp

lemma inductive_step_card  (k : ℕ) :
    Fintype.card { s : Fin (k + 1) → Fin n → 𝔽 // LinearIndependent 𝔽 s } =
      Fintype.card { s : Fin k → Fin n → 𝔽 // LinearIndependent 𝔽 s } *
      ((p ^ (m : ℕ)) ^ n - (p ^ (m : ℕ)) ^k) := by
  rw [Fintype.card_congr (inductiveStepEquiv k), Fintype.card_sigma]
  simp only [complement_card  _, Finset.sum_const]
  rfl

lemma step2  {k : ℕ} (hk : k ≤ n) :
    Fintype.card { s : Fin k → (Fin n → 𝔽) // LinearIndependent 𝔽 s } =
      ∏ i : Fin k, ((p ^ (m : ℕ)) ^ n - (p ^ (m : ℕ)) ^ i.val) := by
  induction' k with k ih
  · simp [LinearIndependent]
  · simp [inductive_step_card k, ih (Nat.le_of_succ_le hk), Fin.prod_univ_succAbove _ k,
      mul_comm]


noncomputable def f (n : ℕ+)
    (s : {s : Fin n → (Fin n → 𝔽) // LinearIndependent 𝔽 s} ): Basis (Fin n) 𝔽 ( Fin n → 𝔽 ) := by
  have hn : n ≤ n := Nat.le_refl n
  have hs := s.2
  have  := step2 (p := p) (k := n) (n := n) (m := m) hn
  haveI : Nonempty (Fin n) := by exact Classical.ofNonempty.proof_1
  have h2 := basisOfLinearIndependentOfCardEqFinrank hs
  simp at h2
  apply h2
  tauto


end Step2
