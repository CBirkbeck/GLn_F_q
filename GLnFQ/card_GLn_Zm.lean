import Mathlib

open Matrix BigOperators

variable (p n r : ℕ) [Fact (Nat.Prime p)]

def proj (h : r ≥ 1): ZMod (p^r) →+* ZMod p := by
  apply ZMod.castHom (dvd_pow_self p (Nat.not_eq_zero_of_lt h))

lemma ker_proj {x : ZMod (p^r) } (h : r ≥ 1): x ∈ (RingHom.ker (proj p r h)) ↔ ∃ (y :ZMod (p^r)), x = p * y := by
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    simp only [proj, ZMod.castHom_apply] at hx
    have : p ∣ x.val := by
      apply (Nat.modEq_zero_iff_dvd).1
      apply (ZMod.nat_cast_eq_nat_cast_iff _ _ _).1
      rw [ZMod.nat_cast_val, Nat.cast_zero, hx]
    rcases this with ⟨y,hy⟩
    use y
    rw [← Nat.cast_mul, ← hy, ZMod.nat_cast_val, ZMod.cast_id', id_eq]
  · intro ⟨y, hy⟩
    rw [RingHom.mem_ker, hy]
    simp only [proj, _root_.map_mul, map_natCast, CharP.cast_eq_zero, ZMod.castHom_apply, zero_mul]

lemma surj (h : r ≥ 1) : Function.Surjective (proj p r h) := ZMod.ringHom_surjective (proj p r h)

lemma unit_proj (h : r ≥ 1) (x : (ZMod (p ^ r))) (hx : IsUnit ((proj p r h) x)) : IsUnit x := by
  rcases hx with ⟨y,hy⟩
  rw [← show ↑(ZMod.val x) = x by simp only [ZMod.nat_cast_val, ZMod.cast_id', id_eq]]
  apply (ZMod.isUnit_iff_coprime x.val (p ^ r)).2
  apply Nat.Coprime.pow_right r _
  apply (ZMod.isUnit_iff_coprime x.val (p)).1
  rw [show ↑(ZMod.val x) = (proj p r h) x by simp [proj]]
  exact ⟨y,hy⟩

def mapGL [Fintype m] [DecidableEq m] [CommRing α] [CommRing β] (f : α →+* β) : GL m α →* GL m β := Units.map (RingHom.toMonoidHom (RingHom.mapMatrix f))

def proj_GL (h : r ≥ 1) : (GL (Fin n) (ZMod (p ^ r))) →* (GL (Fin n) (ZMod p)) := mapGL (proj p r h)

lemma mapMatrix_surj [Fintype m] [DecidableEq m] [CommRing α] [CommRing β] (f : α →+* β) (h : Function.Surjective f) : Function.Surjective (RingHom.mapMatrix f : Matrix m m α →+* Matrix m m β) := by
  intro M
  simp only [Function.Surjective] at h
  use (fun i j => Classical.choose (h (M i j)))
  ext i j
  rw [RingHom.mapMatrix_apply]
  exact Function.surjInv_eq h (M i j)

lemma surj_proj_GL (h : r ≥ 1) : Function.Surjective (proj_GL p n r h) := by
  intro M
  rcases (mapMatrix_surj (proj p r h) (surj p r h)) (M : Matrix (Fin n) (Fin n) (ZMod p)) with ⟨N,hN⟩
  have : IsUnit (Matrix.det N) := by
    apply unit_proj p r h
    rw [RingHom.map_det, hN]
    rw [show det (M : Matrix (Fin n) (Fin n) (ZMod p)) = ↑(Matrix.GeneralLinearGroup.det M) by simp]
    rcases (Group.isUnit (GeneralLinearGroup.det M)) with ⟨u,hu⟩
    use u
    exact congrArg Units.val hu
  use Matrix.GeneralLinearGroup.mk'' N this
  ext i j
  exact congrFun (congrFun hN i) j

lemma proj_coe {M : GL (Fin n) (ZMod (p ^ r))} (h : r ≥ 1): ((proj_GL p n r h) M : Matrix (Fin n) (Fin n) (ZMod (p))) = RingHom.toMonoidHom (RingHom.mapMatrix (proj p r h)) M := by
  rfl

lemma ker_proj_GL {M : GL (Fin n) (ZMod (p ^ r))} (h : r ≥ 1): M ∈ (MonoidHom.ker (proj_GL p n r h)) ↔ ∃ (N : Matrix (Fin n) (Fin n) (ZMod (p ^ r))), M = (1 : Matrix (Fin n) (Fin n) (ZMod (p ^ r))) + p • N := by
  constructor
  · intro hM
    rw [MonoidHom.mem_ker] at hM
    have proj_coeff (i j : Fin n): (proj p r h) ((M - (1: Matrix (Fin n) (Fin n) (ZMod (p ^ r)))) i j) = 0 := by
      simp
      have : ((proj_GL p n r h) M) i j = (proj p r h) (M i j) := by
        simp only [proj_GL, mapGL, RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe,
          RingHom.mapMatrix_apply, map_apply]
      rw [← this, hM]
      by_cases hij : i=j
      simp [hij]
      simp [hij]
    have ker_proj_coeff (i j : Fin n) : ∃ (y :ZMod (p^r)), ((M - (1: Matrix (Fin n) (Fin n) (ZMod (p ^ r)))) i j) = p * y := by
      apply (ker_proj p r h).1
      rw [RingHom.mem_ker]
      exact proj_coeff i j
    use fun i j ↦ Classical.choose (ker_proj_coeff i j)
    ext i j
    simp only [sub_apply, add_apply, Matrix.smul_apply]
    rw [nsmul_eq_mul, ← Classical.choose_spec (ker_proj_coeff i j), sub_apply, add_sub_cancel]
  · intro ⟨N,hN⟩
    rw [MonoidHom.mem_ker]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [proj_GL, mapGL]
    rw [hN, add_apply, map_add]
    by_cases hij : i=j
    simp [hij]
    simp [hij]

lemma proj_p_zero (N : Matrix (Fin n) (Fin n) (ZMod (p ^ r))): (RingHom.mapMatrix (proj p r h)) (p • N) = 0 := by
  ext i j
  simp only [ _root_.map_mul, map_natCast, RingHom.mapMatrix_apply, zero_apply]
  simp only [map, smul_apply, nsmul_eq_mul, _root_.map_mul, map_natCast, CharP.cast_eq_zero,
    zero_mul, of_apply]

lemma proj_p_add_one (N : Matrix (Fin n) (Fin n) (ZMod (p ^ r))): (RingHom.mapMatrix (proj p r h)) (1 + p • N) = 1 := by
  rw [map_add]
  rw [proj_p_zero]
  simp

lemma GL_mk_coe (S : Matrix (Fin n) (Fin n) (ZMod (p ^ r))) (hS : IsUnit (Matrix.det S)): ((Matrix.GeneralLinearGroup.mk'' S hS) : Matrix (Fin n) (Fin n) (ZMod (p ^ r))) = S := rfl

noncomputable def equiv_ker_matrix (h : r ≥ 1) : MonoidHom.ker (proj_GL p n r h) ≃ { M :Matrix (Fin n) (Fin n) ((ZMod (p ^ r ))) // ∃ (N:Matrix (Fin n) (Fin n) ((ZMod (p ^ r )))), M = p • N} where
  toFun := by
    intro ⟨M, hM⟩
    use (M - 1)
    rcases ((ker_proj_GL p n r h).1 hM) with ⟨N,hN⟩
    use N
    simp [hN]
  invFun := by
    intro ⟨M,hM⟩
    have : IsUnit (Matrix.det (1 + M)) := by
      apply unit_proj p r h (Matrix.det (1 + M))
      rcases hM with ⟨N,hN⟩
      rw [hN]
      rw [RingHom.map_det (proj p r h) (1 + p • N)]
      rw [proj_p_add_one p n _]
      simp
    set L := Matrix.GeneralLinearGroup.mk'' (1 + M) this
    have : L ∈ (MonoidHom.ker (proj_GL p n r h)) := by
      apply (ker_proj_GL p n r h).2
      rcases hM with ⟨N,hN⟩
      use N
      rw [← hN]
      rw [GL_mk_coe]
    use L
  left_inv := by
    intro ⟨M, hM⟩
    simp
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp
    rw [GL_mk_coe]
  right_inv := by
    intro ⟨M, hM⟩
    rw [Subtype.mk.injEq, GL_mk_coe, add_sub_cancel_left]

lemma coeff_p (M :Matrix (Fin n) (Fin n) (ZMod (p ^ r))) (hM :∃ N , M = p • N) (i j : Fin n): ∃ a, M i j = p * a := by
  rcases hM with ⟨N,hN⟩
  use N i j
  rw [hN]
  simp

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
    simp
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
      simp
      symm
      have : p * q = p ^ r := by
        simp [q]
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
    simp [q]
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
        simp [hy]
    · simp
  rcases this with ⟨a,ha⟩
  use (a : Fin (p ^ (r-1)))
  simp [fin_pZpr]
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
      simp
      exact apr
    rw [han, Int.cast_ofNat, Int.cast_ofNat, Fin.val_nat_cast, ← anpr]
  rw [← this]
  simp only [Int.cast_mul, Int.cast_ofNat]

lemma bij_fin_pZpr (h : r ≥ 1) : Function.Bijective (fin_pZpr p r) := ⟨inj_fin_pZpr p r h, surj_fin_pZpr p r h⟩

lemma card_Mn_pZpr (h : r ≥ 1) : Fintype.card ((Fin n) → (Fin n) → { x : (ZMod (p ^ r )) // ∃ (y : (ZMod (p ^ r ))), x = p * y}) = p ^ ((r - 1) * n^2) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
  rw [← Fintype.card_of_bijective (bij_fin_pZpr p r h), Fintype.card_fin]
  ring

lemma card_GL_ker (h : r ≥ 1) : Fintype.card (MonoidHom.ker (proj_GL p n r h)) = p ^ ((r - 1) * n^2) := by
  rw [← card_Mn_pZpr p n r h]
  rw [← Fintype.card_congr (equiv_matrix_pZpr p n r)]
  rw [Fintype.card_congr (equiv_ker_matrix p n r h)]

lemma card_first_iso [Group G] [Fintype G] [Group H] [Fintype H]
  (φ : G →* H) [Fintype ↥(MonoidHom.ker φ)] [DecidablePred fun a => a ∈ MonoidHom.ker φ] (hφ : Function.Surjective ⇑φ) : Fintype.card G  = (Fintype.card H) * (Fintype.card (MonoidHom.ker φ)):= by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker φ)]
  have : Fintype.card (G ⧸ MonoidHom.ker φ)  = Fintype.card H := by
    have : G ⧸ MonoidHom.ker φ ≃ H := QuotientGroup.quotientKerEquivOfSurjective _ hφ
    rw [← Fintype.card_congr this]
  rw [this]

lemma card_GL_Zp : Fintype.card (GL (Fin n) (ZMod p)) =
        ∏ i : (Fin n), (p ^ n - p ^ i.val) := by
  sorry

lemma card_GL_Zpr {r : ℕ} (h : r ≥ 1): Fintype.card (GL (Fin n) (ZMod (p ^ r))) =
        p ^ ((r - 1) * n^2) * ∏ i : (Fin n), (p ^ n - p ^ i.val) := by
    rw [← card_GL_Zp]
    rw [card_first_iso (proj_GL p n r h) (surj_proj_GL p n r h)]
    rw [card_GL_Zp]
    rw [card_GL_ker]
    ring
