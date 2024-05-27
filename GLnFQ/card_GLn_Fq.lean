import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Tactic.Have

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

lemma card_linearIndependent :
    Fintype.card { s : Fin n → (Fin n → 𝔽) // LinearIndependent 𝔽 s } =
      ∏ i : Fin n, (q ^ (n) - q ^ (i : ℕ)) := by
  rw [step2 _ _  ]
  rfl

variable (R : Type*) [CommRing R]

def GLequiv : GL (Fin n) R ≃* (((Fin n) → R) ≃ₗ[R] ((Fin n) → R)) :=
  MulEquiv.trans
    Matrix.GeneralLinearGroup.toLinear
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R _)

def Basis_equiv : Basis (Fin n) R ((Fin n) → R) ≃ ((Fin n) → R) ≃ₗ[R] ((Fin n) →₀ R) where
  toFun := Basis.repr
  invFun := Basis.ofRepr
  left_inv := fun b ↦ by cases b; rfl
  right_inv := fun b ↦ rfl

noncomputable def equiv_finsupp : ((Fin n) → R) ≃ₗ[R] ((Fin n) →₀ R) := by
  exact LinearEquiv.symm (Finsupp.linearEquivFunOnFinite R R (Fin n))

noncomputable def equiv_linmap: (((Fin n) → R) ≃ₗ[R] ((Fin n) → R)) ≃
    (((Fin n) → R) ≃ₗ[R] ((Fin n) →₀ R)) where
  toFun := fun f ↦ (f.trans (equiv_finsupp n R)  : (((Fin n) → R) ≃ₗ[R] ((Fin n) →₀ R)))
  invFun := fun f ↦ (f.trans (equiv_finsupp n R).symm  : (((Fin n) → R) ≃ₗ[R] ((Fin n) → R)))
  left_inv := congrFun rfl
  right_inv := by
    apply congrFun
    ext
    rfl

noncomputable def equiv_GL_basis : GL (Fin n) R ≃ Basis (Fin n) R ((Fin n) → R) := by
  apply Equiv.trans (GLequiv _ _).toEquiv
  apply Equiv.trans (equiv_linmap _ _)
  exact (Basis_equiv n R).symm

noncomputable def equiv_basis_linearindependent (hn : 0 < n) : Basis (Fin n) 𝔽 ((Fin n) → 𝔽) ≃
    { s : Fin n → (Fin n → 𝔽) // LinearIndependent 𝔽 s } where
  toFun := fun b ↦ ⟨b,Basis.linearIndependent _⟩
  invFun := by
    intro ⟨s,hs⟩
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hn
    apply basisOfLinearIndependentOfCardEqFinrank hs
    simp only [Fintype.card_fin, FiniteDimensional.finrank_fintype_fun_eq_card]
  left_inv := by
    intro b
    apply DFunLike.ext'
    simp only [coe_basisOfLinearIndependentOfCardEqFinrank]
  right_inv := by
    intro ⟨s,hs⟩
    simp only [coe_basisOfLinearIndependentOfCardEqFinrank]

noncomputable instance fintype : Fintype (GL (Fin n) 𝔽) := by
    exact Fintype.ofFinite (GL (Fin n) 𝔽)

noncomputable instance : Fintype (Basis (Fin n) 𝔽 ((Fin n) → 𝔽)) :=
    Fintype.ofEquiv _ (equiv_GL_basis n 𝔽)

lemma card_GL : Fintype.card (GL (Fin n) 𝔽) =
        ∏ i : (Fin n), (q ^ (n) - q ^ ( i : ℕ )) := by
    by_cases hn : n = 0
    · rw [hn]
      simp only [Fintype.card_unique, Finset.univ_eq_empty, mul_zero, pow_zero,
      Finset.prod_empty]
    · rw [Fintype.card_congr (equiv_GL_basis n 𝔽), ← (card_linearIndependent n),
      Fintype.card_congr (equiv_basis_linearindependent n (Nat.pos_of_ne_zero hn))]
