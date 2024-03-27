import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.LinearAlgebra.Basis

variable (R : Type) [CommRing R]
variable (M : Type) [AddCommGroup M] [Module R M]
variable (n : Type) [Fintype n] [DecidableEq n]

@[simps]
def GLequiv : GL n R ≃* ((n → R) ≃ₗ[R] (n → R)) :=
  MulEquiv.trans
    Matrix.GeneralLinearGroup.toLinear
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R _)

-- `b` is of the form `V ≃ₗ[R] (n →₀ R)`
-- `b` is of the form `(n → R) ≃ₗ[R] (n →₀ R)`

-- Define `g • b`
instance : SMul (GL n R) (Basis n R (n → R)) where
  smul g b :=
  { repr := sorry }

def Basis_equiv : Basis n R (n → R) ≃ (n → R) ≃ₗ[R] (n →₀ R) where
  toFun := Basis.repr
  invFun := Basis.ofRepr
  left_inv := fun b ↦ by cases b; rfl
  right_inv := fun b ↦ rfl

@[simps]
noncomputable
def LinearEquiv.toMatrix (f : M ≃ₗ[R] M)
  (b₁ : Basis n R M) (b₂ : Basis n R M) :
  GL n R where
    val := LinearMap.toMatrix b₁ b₂ f.toLinearMap
    inv := LinearMap.toMatrix b₂ b₁ f.symm.toLinearMap
    val_inv := by
      rw [← LinearMap.toMatrix_comp]
      simp only [comp_coe, symm_trans_self, refl_toLinearMap]
      rw [LinearMap.toMatrix_id]
    inv_val := by
      rw [← LinearMap.toMatrix_comp]
      simp only [comp_coe, self_trans_symm, refl_toLinearMap]
      rw [LinearMap.toMatrix_id]

noncomputable def GL_equiv_Basis : GL n R ≃ Basis n R (n → R) :=
  let B := Pi.basisFun R n
  { toFun := fun g ↦ Basis.ofRepr ((GLequiv R n g).trans B.repr)
    invFun := fun b ↦ LinearEquiv.toMatrix R _ n (LinearEquiv.refl _ _) B b
    left_inv := by
      intro g
      ext : 1
      dsimp [GLequiv]
      ext i j
      dsimp [LinearMap.toMatrix, LinearMap.toMatrix', B, Pi.basisFun]
      simp
    right_inv := by
      intro b
      ext i j : 2
      dsimp [GLequiv]
      dsimp [LinearMap.toMatrix, LinearMap.toMatrix', B, Pi.basisFun]
      simp
      sorry
     }
