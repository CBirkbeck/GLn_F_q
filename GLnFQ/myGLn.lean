import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

open Matrix BigOperators

variable (p n m : ℕ) [Fact (Nat.Prime p)] (hn : n ≠ 0) (hm : m ≠ 0)

variable [Field K] [AddCommGroup V] [Module K V]

noncomputable instance fintype : Fintype (GL (Fin n) (GaloisField p m)) := by
    exact Fintype.ofFinite (GL (Fin n) (GaloisField p m))

lemma card : Fintype.card (GL (Fin n) (GaloisField p m)) =
        ∏ i : (Fin n), (p ^ (m * n) - p ^ (m * i)) := by
    induction' n with n ih
    simp only [Nat.zero_eq, Fintype.card_unique, Finset.univ_eq_empty, mul_zero, pow_zero, zero_mul,
      ge_iff_le, le_refl, tsub_eq_zero_of_le, Finset.prod_const, Finset.card_empty]

    sorry

local notation "𝔽" => (GaloisField p m)

-- lemma bidule (k : ℕ) : Nat.card machin k =  ∏ i : (Fin k), (p ^ (m * n) - p ^ (m * i)) := by
--  sorry

-- L'ensemble des familles libres de k vecteurs de 𝔽^n
def Free (k : ℕ) := { v : Fin k → (Fin n → 𝔽) | LinearIndependent 𝔽 v}

-- La restriction d'une famille de k+1 vecteurs à ses k premiers vecteurs
def Res (k : ℕ) (v : Fin (k+1) → (Fin n → 𝔽)) : (Fin k → (Fin n → 𝔽)) :=
(v ∘ (fun (i : Fin k) ↦ i))

-- La restriction d'une famille libre est libre
lemma res_free_is_free : ∀ (k : ℕ) (v : Fin (k+1) → V),
LinearIndependent K v → LinearIndependent K (v ∘ (fun (i : Fin k) ↦ i)) := by
intro k v h
rw [LinearIndependent.comp]
-- have h2 := Function.Injective (fun (i : Fin k) ↦ i)
-- [LinearIndependent.comp]

-- La restriction d'une famille libre est libre
-- lemma res_free_is_free (k : ℕ) (v : Fin (k+1) → V) :
-- LinearIndependent K v → LinearIndependent K (v ∘ (fun (i : Fin k) ↦ i)) := by
-- intro h1
-- have h2 := Function.Injective (fun (i : Fin k) ↦ i)
-- [LinearIndependent.comp]

/- Calcule le nombre de familles de k vecteurs de 𝔽^n
lemma card_fam (k : ℕ) : Nat.card (Fin k → (Fin n → 𝔽)) = p ^ (m * n * k) := by
rw [Nat.card_fun]
simp
rw [GaloisField.card]
ring
exact hm

lemma linindep_incl_fam (k : ℕ) :
   { v : Fin k → (Fin n → 𝔽) | LinearIndependent 𝔽 v}
    ⊆ { v :Fin k → (Fin n → 𝔽) | true } := by
    exact fun ⦃a⦄ => congrFun rfl

lemma card_linindep_maj (k : ℕ) :
    Nat.card { v : Fin k → (Fin n → 𝔽) | LinearIndependent 𝔽 v}
    ≤ Nat.card (Fin k → (Fin n → 𝔽)) := by
    exact Finite.card_subtype_le fun x => x ∈ {v | LinearIndependent (GaloisField p m) v}
-/

def addable (k : ℕ) (v : Fin k → (Fin n → 𝔽)) :=
{ w : (Fin n → 𝔽) | w ∉ Submodule.span 𝔽 (Set.range v) }

def restriction (k : ℕ) :
{ v : Fin (k+1) → (Fin n → 𝔽) | LinearIndependent 𝔽 v } →
{ β : (Fin k → (Fin n → 𝔽)) → (Fin n → 𝔽) |
∀ v : Fin k → (Fin n → 𝔽), (LinearIndependent 𝔽 v) ∧
(β v ∉ Submodule.span 𝔽 (Set.range v)) } :=
fun v ↦ (fun )

lemma decomposition_linindep_1 (k : ℕ) :
{ v : Fin (k+1) → (Fin n → 𝔽) | LinearIndependent 𝔽 v } ≃
{ β : (Fin k → (Fin n → 𝔽)) → (Fin n → 𝔽) |
∀ v : Fin k → (Fin n → 𝔽), (LinearIndependent 𝔽 v) ∧
(β v ∉ Submodule.span 𝔽 (Set.range v)) } := by
sorry

lemma decomposition_linindep_2 (k : ℕ) :
Nat.card { v : Fin (k+1) → (Fin n → 𝔽) | LinearIndependent 𝔽 v } =
Nat.card { β : (Fin k → (Fin n → 𝔽)) → (Fin n → 𝔽) |
∀ v : Fin k → (Fin n → 𝔽), (LinearIndependent 𝔽 v) ∧
(β v ∉ Submodule.span 𝔽 (Set.range v)) } := by
rw [Nat.card_congr]
apply decomposition_linindep_1

lemma step2 (k : ℕ) :
    Nat.card { v : Fin k → (Fin n → 𝔽) | LinearIndependent 𝔽 v}
    = (Finset.univ : Finset (Fin k)).prod fun i => p ^ (m * k) - p ^ (m * i.val) := by
--    = ∏ i : (Fin k), (p ^ (m * n) - p ^ (m * i)) := by
  induction' k using Nat.recAux with k ih
  simp [LinearIndependent]
  have h := Nat.card { v : Fin (k+1) → (Fin n → 𝔽) | LinearIndependent 𝔽 v}
    = Nat.card { β : (Fin k → (Fin n → 𝔽)) → (Fin n → 𝔽) |
    ∀ v : Fin k → (Fin n → 𝔽), β v ∉ Submodule.span 𝔽 (Set.range v) }
  apply?






-- Nat.card_fun


variable (e : Fin n → 𝔽)

#check Submodule.span 𝔽 ({e} : Set (Fin n → 𝔽))

#check LinearIndependent
#check linearIndependent_unique_iff
#check LinearIndependent.comp
#check linearIndependent_iff_not_smul_mem_span
#check linearIndependent_fin_cons
#check linearIndependent_fin_snoc


--Basis.invertibleToMatrix might be useful to turn it into a question about bases.
