import Mathlib
import GLnFQ.card_GLn_Fq

open Matrix BigOperators

section

def mapGL [Fintype m] [DecidableEq m] [CommRing α] [CommRing β] (f : α →+* β) : GL m α →* GL m β := Units.map (RingHom.toMonoidHom (RingHom.mapMatrix f))

lemma mapGL_injective [Fintype m] [DecidableEq m] [CommRing α] [CommRing β] (f : α →+* β) (h : Function.Injective f): Function.Injective (mapGL f : GL m α → GL m β) := by
    intro M N k
    unfold mapGL at k
    apply @Units.map_injective _ _ _ _ (RingHom.toMonoidHom (RingHom.mapMatrix f)) _ _ _ k
    intro M N g
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply] at g
    ext i j
    apply h
    rw [← @map_apply _ _ _ _ _ f, ← @map_apply _ _ _ _ _ f, g]

lemma mapMatrix_surjective [Fintype m] [DecidableEq m] [CommRing α] [CommRing β] (f : α →+* β) (h : Function.Surjective f) : Function.Surjective (RingHom.mapMatrix f : Matrix m m α →+* Matrix m m β) := by
  intro M
  use (fun i j => Function.surjInv h (M i j))
  ext i j
  rw [RingHom.mapMatrix_apply]
  exact Function.surjInv_eq h (M i j)

lemma mapGL_surjective [Fintype m] [DecidableEq m] [CommRing α] [CommRing β] (f : α →+* β) (h1 : Function.Surjective f) [IsLocalRingHom f]: Function.Surjective (mapGL f : GL m α → GL m β) := by
  intro M
  rcases ((mapMatrix_surjective f h1) (M : Matrix m m β)) with ⟨N,hN⟩
  have : IsUnit (Matrix.det N) := by
    apply (isUnit_map_iff f (det N)).1
    rw [RingHom.map_det, hN]
    rcases (Group.isUnit (GeneralLinearGroup.det M)) with ⟨u,hu⟩
    use u
    exact congrArg Units.val hu
  use Matrix.GeneralLinearGroup.mk'' N this
  ext i j
  exact congrFun (congrFun hN i) j

lemma matrix_prodEquivPi [Fintype m] {r : ι → Type*} [∀ i : ι, Mul (r i)] [∀ i : ι, AddCommMonoid (r i)]: Matrix m m (∀ i, r i) ≃* ( ∀ i, Matrix m m (r i)) where
  toFun M k := fun i j => M i j k
  invFun M := fun i j => (fun k => M k i j)
  left_inv := congrFun rfl
  right_inv := congrFun rfl
  map_mul' M M:= by
    ext
    simp only [Pi.mul_apply]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Finset.sum_apply, Pi.mul_apply]

lemma det_matrix_prod_pi [Fintype m] [DecidableEq m] (r : ι → Type*) [∀ i : ι, CommRing (r i)] (M : Matrix m m (∀ i, r i)) : det M = fun i => det (matrix_prodEquivPi M i) := by
  unfold matrix_prodEquivPi
  ext
  simp only [Matrix.det_apply, Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, MulEquiv.coe_mk, Equiv.coe_fn_mk]

def pi_units (r : ι → Type*) [∀ i : ι, Monoid (r i)] : (∀ i , r i)ˣ ≃* ∀ i, (r i)ˣ where
  toFun := fun p ↦ (fun i ↦ (Units.map (Pi.evalMonoidHom r i)) p)
  invFun u := ⟨fun i ↦ u i, fun i ↦ ↑(u i)⁻¹, by ext; simp, by ext; simp ⟩
  left_inv u := by
    simp only [Units.coe_map, Pi.evalMonoidHom_apply, Units.coe_map_inv, Units.mk_val]
  right_inv u := rfl
  map_mul' u v := rfl

lemma GL_prodEquivPi [Fintype m] [DecidableEq m] (r : ι → Type*) [∀ i : ι, CommRing (r i)]: GL m (∀ i, r i) ≃* ∀ i, GL m (r i) where
  toFun M k:= by
    apply Matrix.GeneralLinearGroup.mk'' (matrix_prodEquivPi M k)
    rw [show det ((matrix_prodEquivPi M k) : Matrix m m (r k)) = (det (M : Matrix m m (∀ i, r i))) k by rw [det_matrix_prod_pi]]
    rw [← GeneralLinearGroup.val_det_apply]
    use ((pi_units r (Matrix.GeneralLinearGroup.det M)) k)
    simp only [pi_units, MulEquiv.coe_mk, Equiv.coe_fn_mk, Units.coe_map,
      GeneralLinearGroup.val_det_apply, Pi.evalMonoidHom_apply]
  invFun M := by
    apply Matrix.GeneralLinearGroup.mk'' (matrix_prodEquivPi.symm (fun i => M i))
    use (pi_units r).symm (fun i ↦ Matrix.GeneralLinearGroup.det (M i))
    unfold pi_units
    rw [det_matrix_prod_pi]
    ext
    unfold matrix_prodEquivPi
    simp only [MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
      GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_inv_det_apply, coe_units_inv,
      det_nonsing_inv, Equiv.coe_fn_mk]
  left_inv M:= by
    simp only [Matrix.GeneralLinearGroup.mk'', nonsingInvUnit, unitOfInvertible, MulEquiv.symm_apply_apply, id_eq, eq_mpr_eq_cast, GeneralLinearGroup.val_det_apply,
      cast_eq, invOf_eq_nonsing_inv, Units.mk_val]
  right_inv M := by
    simp only [GeneralLinearGroup.mk'', nonsingInvUnit, unitOfInvertible, invOf_eq_nonsing_inv,
      MulEquiv.apply_symm_apply, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
      GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_inv_det_apply, id_eq, eq_mpr_eq_cast,
      Units.mk_val]
  map_mul' M N:= by
    simp only [GeneralLinearGroup.mk'', nonsingInvUnit, unitOfInvertible, Units.val_mul,
      _root_.map_mul, Pi.mul_apply, invOf_eq_nonsing_inv]
    ext k i j
    simp only [Pi.mul_apply, Units.val_mul]


def iso_mapGL [Fintype m] [DecidableEq m] [CommRing α] [CommRing β] (f : α ≃+* β) : GL m α ≃* GL m β where
  toFun := mapGL f
  invFun := mapGL f.symm
  left_inv M := by
    unfold mapGL
    ext i j
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, RingHom.coe_coe, map_apply, RingEquiv.symm_apply_apply]
  right_inv M := by
    unfold mapGL
    ext i j
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, RingHom.coe_coe, map_apply, RingEquiv.apply_symm_apply]
  map_mul' := by simp only [_root_.map_mul, forall_const]

end

section

variable (p n r : ℕ) [Fact (Nat.Prime p)]

def proj_ZMod (h : r ≥ 1): ZMod (p^r) →+* ZMod p := by
  apply ZMod.castHom (dvd_pow_self p (Nat.not_eq_zero_of_lt h))

lemma ker_proj_ZMod {x : ZMod (p^r)} (h : r ≥ 1): x ∈ (RingHom.ker (proj_ZMod p r h)) ↔ ∃ (y :ZMod (p^r)), x = p * y := by
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    simp only [proj_ZMod, ZMod.castHom_apply] at hx
    have : p ∣ x.val := by
      apply (Nat.modEq_zero_iff_dvd).1
      apply (ZMod.nat_cast_eq_nat_cast_iff _ _ _).1
      rw [ZMod.nat_cast_val, Nat.cast_zero, hx]
    rcases this with ⟨y,hy⟩
    use y
    rw [← Nat.cast_mul, ← hy, ZMod.nat_cast_val, ZMod.cast_id', id_eq]
  · intro ⟨y, hy⟩
    rw [RingHom.mem_ker, hy]
    simp only [proj_ZMod, _root_.map_mul, map_natCast, CharP.cast_eq_zero, ZMod.castHom_apply, zero_mul]

lemma proj_ZMod_surj (h : r ≥ 1) : Function.Surjective (proj_ZMod p r h) := ZMod.ringHom_surjective (proj_ZMod p r h)

instance proj_ZMod_LocalRingHom : IsLocalRingHom (proj_ZMod p r h) where
  map_nonunit x hx:= by
    rcases hx with ⟨y,hy⟩
    rw [← show ↑(ZMod.val x) = x by simp only [ZMod.nat_cast_val, ZMod.cast_id', id_eq]]
    apply (ZMod.isUnit_iff_coprime x.val (p ^ r)).2
    apply Nat.Coprime.pow_right r _
    apply (ZMod.isUnit_iff_coprime x.val (p)).1
    rw [show ↑(ZMod.val x) = (proj_ZMod p r h) x by simp [proj_ZMod]]
    exact ⟨y,hy⟩

def proj_GL (h : r ≥ 1) : (GL (Fin n) (ZMod (p ^ r))) →* (GL (Fin n) (ZMod p)) := mapGL (proj_ZMod p r h)

lemma surj_GL (h : r ≥ 1) : Function.Surjective (proj_GL p n r h) := mapGL_surjective _ (proj_ZMod_surj p r h)

lemma proj_ZMod_coe {M : GL (Fin n) (ZMod (p ^ r))} (h : r ≥ 1): ((proj_GL p n r h) M : Matrix (Fin n) (Fin n) (ZMod (p))) = RingHom.toMonoidHom (RingHom.mapMatrix (proj_ZMod p r h)) M := by
  rfl

lemma ker_proj_GL {M : GL (Fin n) (ZMod (p ^ r))} (h : r ≥ 1): M ∈ (MonoidHom.ker (proj_GL p n r h)) ↔ ∃ (N : Matrix (Fin n) (Fin n) (ZMod (p ^ r))), M = (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ r))) + p • N := by
  constructor
  · intro hM
    rw [MonoidHom.mem_ker] at hM
    have proj_ZMod_coeff (i j : Fin n): (proj_ZMod p r h) ((M - (1: Matrix (Fin n) (Fin n) (ZMod (p ^ r)))) i j) = 0 := by
      simp only [sub_apply, map_sub]
      have : ((proj_GL p n r h) M) i j = (proj_ZMod p r h) (M i j) := by
        simp only [proj_GL, mapGL, RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe,
          RingHom.mapMatrix_apply, map_apply]
      rw [← this, hM]
      by_cases hij : i=j
      · simp only [hij, Units.val_one, one_apply_eq, _root_.map_one, sub_self]
      · simp only [Units.val_one, ne_eq, hij, not_false_eq_true, one_apply_ne, map_zero, sub_self]
    have ker_proj_ZMod_coeff (i j : Fin n) : ∃ (y :ZMod (p^r)), ((M - (1: Matrix (Fin n) (Fin n) (ZMod (p ^ r)))) i j) = p * y := by
      apply (ker_proj_ZMod p r h).1
      rw [RingHom.mem_ker]
      exact proj_ZMod_coeff i j
    use fun i j ↦ Classical.choose (ker_proj_ZMod_coeff i j)
    ext i j
    simp only [sub_apply, add_apply, Matrix.smul_apply]
    rw [nsmul_eq_mul, ← Classical.choose_spec (ker_proj_ZMod_coeff i j), sub_apply, add_sub_cancel]
  · intro ⟨N,hN⟩
    rw [MonoidHom.mem_ker]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [proj_GL, mapGL, RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, map_apply, Units.val_one]
    rw [hN, add_apply, map_add]
    by_cases hij : i=j
    · simp only [hij, one_apply_eq, _root_.map_one, smul_apply, nsmul_eq_mul, _root_.map_mul,
      map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
    · simp only [ne_eq, hij, not_false_eq_true, one_apply_ne, map_zero, smul_apply, nsmul_eq_mul,
      _root_.map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]

lemma proj_p_zero (N : Matrix (Fin n) (Fin n) (ZMod (p ^ r))): (RingHom.mapMatrix (proj_ZMod p r h)) (p • N) = 0 := by
  ext i j
  simp only [ _root_.map_mul, map_natCast, RingHom.mapMatrix_apply, zero_apply]
  simp only [map, smul_apply, nsmul_eq_mul, _root_.map_mul, map_natCast, CharP.cast_eq_zero,
    zero_mul, of_apply]

lemma proj_p_add_one (N : Matrix (Fin n) (Fin n) (ZMod (p ^ r))): (RingHom.mapMatrix (proj_ZMod p r h)) (1 + p • N) = 1 := by
  rw [map_add, proj_p_zero]
  simp only [_root_.map_one, add_zero]

lemma GL_mk_coe (S : Matrix (Fin n) (Fin n) (ZMod (p ^ r))) (hS : IsUnit (Matrix.det S)): ((Matrix.GeneralLinearGroup.mk'' S hS) : Matrix (Fin n) (Fin n) (ZMod (p ^ r))) = S := rfl

noncomputable def equiv_ker_matrix (h : r ≥ 1) : MonoidHom.ker (proj_GL p n r h) ≃ { M :Matrix (Fin n) (Fin n) ((ZMod (p ^ r ))) // ∃ (N:Matrix (Fin n) (Fin n) ((ZMod (p ^ r )))), M = p • N} where
  toFun := by
    intro ⟨M, hM⟩
    use (M - 1)
    rcases ((ker_proj_GL p n r h).1 hM) with ⟨N,hN⟩
    use N
    simp only [hN, nsmul_eq_mul, add_sub_cancel_left]
  invFun := by
    intro ⟨M,hM⟩
    have : IsUnit (Matrix.det (1 + M)) := by
      rw [← isUnit_map_iff (proj_ZMod p r h) (Matrix.det (1 + M))]
      rcases hM with ⟨N,hN⟩
      rw [hN, RingHom.map_det (proj_ZMod p r h) (1 + p • N), proj_p_add_one p n _]
      simp only [det_one, isUnit_one]
    set L := Matrix.GeneralLinearGroup.mk'' (1 + M) this
    have : L ∈ (MonoidHom.ker (proj_GL p n r h)) := by
      apply (ker_proj_GL p n r h).2
      rcases hM with ⟨N,hN⟩
      use N
      rw [← hN, GL_mk_coe]
    use L
  left_inv := by
    intro ⟨M, hM⟩
    simp only [add_sub_cancel, Subtype.mk.injEq]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [GL_mk_coe]
  right_inv _ := by
    rw [Subtype.mk.injEq, GL_mk_coe, add_sub_cancel_left]

lemma coeff_p (M :Matrix (Fin n) (Fin n) (ZMod (p ^ r))) (hM :∃ N , M = p • N) (i j : Fin n): ∃ a, M i j = p * a := by
  rcases hM with ⟨N,hN⟩
  use N i j
  rw [hN]
  simp only [smul_apply, nsmul_eq_mul]

noncomputable def equiv_matrix_pZpr : { M :Matrix (Fin n) (Fin n) ((ZMod (p ^ r ))) // ∃ (N:Matrix (Fin n) (Fin n) ((ZMod (p ^ r )))), M = p • N} ≃ ((Fin n) → (Fin n) → { x : (ZMod (p ^ r )) // ∃ (y : (ZMod (p ^ r ))), x = p * y}) where
  toFun := by
    intro ⟨M,hM⟩
    intro i j
    use p * Classical.choose (coeff_p p n r M hM i j)
    use Classical.choose (coeff_p p n r M hM i j)
  invFun := by
    intro N
    use fun i j ↦ (N i j)
    use fun i j ↦ Classical.choose ((N i j).2)
    ext i j
    rw [Classical.choose_spec ((N i j).2)]
    simp only [smul_apply, nsmul_eq_mul]
  left_inv := by
    intro ⟨M,hM⟩
    simp only [Subtype.mk.injEq]
    ext i j
    rw [← Classical.choose_spec (coeff_p p n r M hM i j)]
  right_inv := by
    intro N
    simp
    ext i j
    simp
    rw [← Classical.choose_spec ((N i j).2)]

def fin_pZpr : Fin (p ^ (r - 1)) → { x : (ZMod (p ^ r )) // ∃ (y : (ZMod (p ^ r ))), x = p * y} := by
  intro y
  use p * y
  use y

lemma inj_fin_pZpr (h : r ≥ 1) : Function.Injective (fin_pZpr p r) := by
  intro x y
  simp [fin_pZpr]
  intro hxy
  let q:= p ^ (r-1)
  have qdiv: ( q : ℤ) ∣ x - y := by
    apply Int.dvd_of_mul_dvd_mul_left _
    · rw [show (p : ℤ) * (x - y) = p * x - p * y by ring]
      apply (ZMod.int_cast_eq_int_cast_iff_dvd_sub _ _ (p*q)).1
      simp only [Int.cast_mul, Int.cast_ofNat]
      symm
      have : p * q = p ^ r := by
        simp only [q]
        rw [mul_pow_sub_one (Nat.not_eq_zero_of_lt h)]
      rw [this]
      exact hxy
    · apply Int.ofNat_ne_zero.2
      apply Nat.Prime.ne_zero
      apply Fact.elim
      assumption
  have : (x : ℤ) = (y : ℤ) := by
    apply Int.eq_of_sub_eq_zero
    apply Int.eq_zero_of_abs_lt_dvd qdiv
    simp only [Nat.cast_pow, q]
    apply (abs_sub_lt_iff ).2
    constructor <;> linarith [Fin.isLt x, Fin.isLt y]
  apply Fin.eq_of_val_eq
  apply Int.ofNat_inj.1
  rw [this]

lemma surj_fin_pZpr (h : r ≥ 1) : Function.Surjective (fin_pZpr p r) := by
  intro ⟨x,hx⟩
  rcases hx with ⟨y,hy⟩
  let q := p ^ r
  have : (p : ℤ) ∣ x.val := by
    rw [show (x.val : ℤ) = (x.val - p * y.val) + ( p * y.val) by ring]
    apply dvd_add
    · apply Dvd.dvd.trans
      · apply dvd_pow_self
        apply Nat.not_eq_zero_of_lt h
      · rw [show (p : ℤ) ^ r = q by simp [q]]
        apply (ZMod.int_cast_eq_int_cast_iff_dvd_sub _ _ _).1
        simp only [ZMod.nat_cast_val, Int.cast_mul, Int.cast_ofNat, ZMod.int_cast_cast,
          ZMod.cast_id', id_eq, hy, ZMod.cast_mul', ZMod.cast_nat_cast']
    · simp only [ZMod.nat_cast_val, dvd_mul_right]
  rcases this with ⟨a,ha⟩
  use (a : Fin (p ^ (r-1)))
  simp only [fin_pZpr, Subtype.mk.injEq]
  rw [show x = ↑(x.val : ℤ) by simp]
  rw [ha]
  have : (a : ZMod (p ^ r))= (a : Fin (p ^ (r-1))).val := by
    have p_pos : (p : ℤ) > 0 := by
      apply Int.ofNat_pos.2
      apply Nat.Prime.pos
      apply Fact.elim
      assumption
    have a_nonneg : a ≥ 0 := by
      apply le_of_mul_le_mul_left
      rw [mul_zero, ← ha]
      apply Int.ofNat_nonneg
      exact p_pos
    have apr : a < (p ^ (r-1)) := by
      apply Int.lt_of_mul_lt_mul_left
      rw [← ha, mul_pow_sub_one (Nat.not_eq_zero_of_lt h)]
      rw [show (p : ℤ) ^ r = q by simp [q]]
      apply (Int.ofNat_lt).2
      · exact ZMod.val_lt _
      · exact Int.le_of_lt p_pos
    have an : ∃ (n:ℕ), a=↑ n := by
      use Int.natAbs a
      rw [Int.natAbs_of_nonneg a_nonneg]
    rcases an with ⟨n,han⟩
    have anpr : n=n % p ^ (r - 1) := by
      rw [Nat.mod_eq_of_lt]
      apply (Int.ofNat_lt).1
      rw [← han]
      simp only [Nat.cast_pow]
      exact apr
    rw [han, Int.cast_ofNat, Int.cast_ofNat, Fin.val_nat_cast, ← anpr]
  rw [← this]
  simp only [Int.cast_mul, Int.cast_ofNat]

lemma bij_fin_pZpr (h : r ≥ 1) : Function.Bijective (fin_pZpr p r) := ⟨inj_fin_pZpr p r h, surj_fin_pZpr p r h⟩

lemma card_Mn_pZpr (h : r ≥ 1) : Fintype.card ((Fin n) → (Fin n) → { x : (ZMod (p ^ r )) // ∃ (y : (ZMod (p ^ r ))), x = p * y}) = p ^ ((r - 1) * n^2) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
  rw [← Fintype.card_of_bijective (bij_fin_pZpr p r h), Fintype.card_fin]
  ring


noncomputable instance instGLpr [Fact (Nat.Prime p)]: Fintype (GL (Fin n) (ZMod (p ^ r))) := Fintype.ofFinite _

lemma card_GL_ker (h : r ≥ 1) : Fintype.card (MonoidHom.ker (proj_GL p n r h)) = p ^ ((r - 1) * n^2) := by
  rw [← card_Mn_pZpr p n r h, ← Fintype.card_congr (equiv_matrix_pZpr p n r), Fintype.card_congr (equiv_ker_matrix p n r h)]

lemma card_first_iso [Group G] [Fintype G] [Group H] [Fintype H]
  (φ : G →* H) [Fintype ↥(MonoidHom.ker φ)] [DecidablePred fun a => a ∈ MonoidHom.ker φ] (hφ : Function.Surjective ⇑φ) : Fintype.card G  = (Fintype.card H) * (Fintype.card (MonoidHom.ker φ)):= by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker φ)]
  have : Fintype.card (G ⧸ MonoidHom.ker φ)  = Fintype.card H := by
    have : G ⧸ MonoidHom.ker φ ≃ H := QuotientGroup.quotientKerEquivOfSurjective _ hφ
    rw [← Fintype.card_congr this]
  rw [this]

lemma card_GL_Zp : Fintype.card (GL (Fin n) (ZMod p)) =
        ∏ i : (Fin n), (p ^ n - p ^ i.val) := by
  rw [card_GL, ZMod.card]

lemma card_GL_Zpr {r : ℕ} (h : r ≥ 1): Fintype.card (GL (Fin n) (ZMod (p ^ r))) =
        p ^ ((r - 1) * n^2) * ∏ i : (Fin n), (p ^ n - p ^ i.val) := by
    rw [← card_GL_Zp, card_first_iso (proj_GL p n r h) (surj_GL p n r h), card_GL_Zp, card_GL_ker]
    ring

end

section

variable (N : ℕ) (h : N ≠ 0)

instance fin_ZMod : Fintype (ZMod (N)) := by
  have : NeZero N := by exact { out := h }
  apply ZMod.fintype N

noncomputable instance : (i : { x // x ∈ N.primeFactors }) → Fintype (GL (Fin n) (ZMod (↑i ^ (Nat.factorization N) ↑i))) := by
  intro ⟨p,hp⟩
  have : Fact (Nat.Prime p) := ⟨(Nat.prime_of_mem_primeFactors hp)⟩
  apply instGLpr

instance : (a : { x // x ∈ N.primeFactors }) → Fintype (ZMod (↑a ^ (Nat.factorization N) ↑a)) := by
  intro ⟨x,hx⟩
  have : NeZero x := NeZero.of_pos (Nat.pos_of_mem_primeFactors hx)
  apply ZMod.fintype

instance : Fintype (GL (Fin n) ((i : { x // x ∈ (N).primeFactors }) → ZMod (↑i ^ (Nat.factorization N) ↑i))):= instFintypeUnits

lemma card_GL_ZMod : Nat.card (GL (Fin n) (ZMod (N))) = Finsupp.prod (Nat.factorization (N)) fun x x_1 => (x ^ ((x_1 - 1) * (n)^2) * ∏ i : (Fin n), (x ^ (n) - x ^ i.val)) := by
  set fun_card:= fun (x x_1 : ℕ) => (x ^ ((x_1 - 1) * (n)^2) * ∏ i : (Fin n), (x ^ (n) - x ^ i.val))
  have N_primes: N = ∏ p in N.primeFactors, p ^ (Nat.factorization N) p := by
    conv =>
      enter [1]
      rw [← (Nat.factorization_prod_pow_eq_self h)]
  conv =>
    enter [1]
    rw [N_primes]
  have equiv_ZMod: ZMod (∏ x in N.primeFactors, x ^ (Nat.factorization N) x) ≃+* ((i : { x // x ∈ N.primeFactors }) → ZMod (↑i ^ (Nat.factorization N) ↑i)):= by
    rw [←(Finset.prod_subtype N.primeFactors ?h fun a => a ^ (Nat.factorization N) a).symm]
    · apply ZMod.prodEquivPi
      intro ⟨x,hx⟩ ⟨y,hy⟩ hxy
      apply Nat.Coprime.pow
      rw [ne_eq, Subtype.mk.injEq] at hxy
      exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hx) (Nat.prime_of_mem_primeFactors hy)).2 hxy
    · exact fun x => Eq.to_iff rfl
  rw [Nat.card_eq]
  have : Finite (GL (Fin n) (ZMod (∏ p in N.primeFactors, p ^ (Nat.factorization N) p))) := by
    rw [← N_primes]
    have : Fintype (ZMod N) := fin_ZMod N h
    refine instFiniteUnits
  simp only [this, Fintype.card_of_bijective (MulEquiv.bijective (iso_mapGL equiv_ZMod)), Fintype.card_of_bijective (MulEquiv.bijective (GL_prodEquivPi _)), Fintype.card_pi]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  rw[ ←(Finset.prod_subtype N.primeFactors ?h fun a => (fun_card a ((Nat.factorization N) a))).symm]
  apply Finset.prod_congr
  · rfl
  · intro ⟨x,hx⟩
    simp only [Finset.univ_eq_attach, Finset.mem_attach, forall_true_left]
    have : Fact (Nat.Prime x) := ⟨(Nat.prime_of_mem_primeFactors hx)⟩
    simp only [fun_card]
    rw [← @card_GL_Zpr x n _ ((Nat.factorization N) x)]
    apply Nat.one_le_iff_ne_zero.mpr
    exact Finsupp.mem_support_iff.1 hx

end
