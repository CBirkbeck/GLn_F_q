import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

open Matrix BigOperators

variable (p n m : ℕ) [Fact (Nat.Prime p)]

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

#check Submodule.span 𝔽 ({v} : Set (Fin n → 𝔽))




--Basis.invertibleToMatrix might be useful to turn it into a question about bases.
