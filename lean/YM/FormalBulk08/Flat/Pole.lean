import YM.FormalBulk08.Flat.Smoothing

/-! Pole and real reciprocal estimates. Norm of momentum here is the native pi norm on Momentum. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Precision RG Next.Free UVExtension.Free
open scoped Topology BigOperators

lemma product_move (x y u v : ℂ) {dx dy A B : ℝ}
    (hx : ‖x-u‖≤dx) (hy : ‖y-v‖≤dy) (ha : ‖x‖≤A) (hb : ‖v‖≤B) :
    ‖x*y-u*v‖ ≤ A*dy + dx*B := by
  rw [show x*y-u*v=x*(y-v)+(x-u)*v by ring]
  exact (norm_add_le ..).trans (add_le_add ((norm_mul ..).trans_le (mul_le_mul ha hy (norm_nonneg _) ((norm_nonneg _).trans ha))) ((norm_mul ..).trans_le (mul_le_mul hx hb (norm_nonneg _) ((norm_nonneg _).trans hx))))

lemma inv_move {x y : ℂ} {A B D : ℝ} (ha : 0<A) (hb : 0<B) (hx : A ≤ ‖x‖)
    (hy : B ≤ ‖y‖) (hd : ‖x-y‖≤D) : ‖x⁻¹-y⁻¹‖ ≤ D/(A*B) := by
  have h := ha.trans_le hx
  have hg := hb.trans_le hy
  rw [show x⁻¹-y⁻¹= -(x-y)/(x*y) by field_simp [norm_pos_iff.mp h,norm_pos_iff.mp hg]; ring,
    norm_div,norm_neg,norm_mul]
  exact div_le_div₀ ((norm_nonneg _).trans hd) hd (mul_pos ha hb) (mul_le_mul hx hy hb.le h.le)

lemma chip_real_error (z : ℂ) (hz : z.im=0) :
    ‖chip z-Complex.I*z‖ ≤ 2*‖z‖^2 := by
  have h : ‖Complex.I*z‖=‖z‖ := by rw [norm_mul,Complex.norm_I,one_mul]
  by_cases ht : ‖z‖≤1
  · have he : ‖chip z-Complex.I*z‖≤‖Complex.I*z‖^2 := Complex.norm_exp_sub_one_sub_id_le (h.trans_le ht)
    rw [h] at he; exact he.trans (le_mul_of_one_le_left (by positivity) (by norm_num))
  apply (norm_sub_le ..).trans ((add_le_add (real_chip z hz) h.le).trans ?_)
  nlinarith

lemma seed_real_bound (L : Side) (p : Momentum) (hp : physical p) (a : Axis) :
    ‖seedQ L p a‖ ≤ ‖p‖ ∧ ‖seedQ L p a-Complex.I*p a‖ ≤ 2*‖p‖^2/L.val := by
  have hL := side_pos L
  let w := narrow L p a; have hw : w.im=0 := (physical_iff _).1 (narrow_real L hp) a
  have he : (L.val:ℂ)*w=p a := by unfold w; rw [narrow_apply,mul_div_cancel₀ _ (side_ne L)]
  have hb : (L.val:ℝ)*‖w‖≤‖p‖ := by rw [← Complex.norm_natCast, ← norm_mul, he]; exact norm_le_pi_norm _ _
  refine ⟨(norm_mul (L.val:ℂ) (chip w)).le.trans ?_,?_⟩
  · rw [Complex.norm_natCast]; exact (mul_le_mul_of_nonneg_left (real_chip w hw) hL.le).trans hb
  rw [show seedQ L p a-Complex.I*p a=(L.val:ℂ)*(chip w-Complex.I*w) by rw [mul_sub,mul_left_comm (L.val:ℂ) Complex.I, he]; rfl,
    norm_mul,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left (chip_real_error _ hw) hL.le).trans
  rw [le_div_iff₀ hL]; nlinarith only [pow_le_pow_left₀ (mul_nonneg hL.le (norm_nonneg w)) hb 2]

lemma physical_minus (p : Momentum) (hp : physical p) : physical (-p) := (star_neg p).trans (congr_arg Neg.neg hp)

lemma divisor_difference (L M : Side) (hlt : L.val≤M.val) (p : Momentum) (hp : physical p) :
    ‖divisor L p-divisor M p‖ ≤ 32*‖p‖^3/L.val := by
  have H (p : Momentum) (hp : physical p) (a : Axis) : ‖seedQ L p a-seedQ M p a‖ ≤ 4*‖p‖^2/L.val := by
    apply (norm_sub_le_norm_sub_add_norm_sub _ (Complex.I*p a) _).trans
    rw [norm_sub_rev (Complex.I*p a)]
    apply (add_le_add (seed_real_bound L p hp a).2 (seed_real_bound M p hp a).2).trans
    calc
      _ ≤ 2*‖p‖^2/L.val+2*‖p‖^2/L.val := by gcongr
      _ = _ := by ring
  unfold divisor; rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _ : Axis, 8*‖p‖^3/L.val := Finset.sum_le_sum fun a _=> by
      have he := product_move _ _ _ _ (H p hp a) (H (-p) (physical_minus p hp) a)
        (seed_real_bound L p hp a).1 (seed_real_bound M _ (physical_minus p hp) a).1
      rw [norm_neg] at he; exact he.trans_eq (by ring)
    _ = _ := by simp only [Axis,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; ring

lemma steps_incr (S : Schedule) (d D : ℕ) (h : d≤D) (i : ℕ) :
    (S.steps i d).val ≤ (S.steps i D).val := by
  induction D,h using Nat.le_induction with
  | base => exact le_rfl
  | succ D hd ih =>
    have hx := step_three S i D
    have hv := side_pos (S.steps i D)
    apply le_trans ih
    exact_mod_cast (show ((S.steps i D).val:ℝ)≤(S.steps i (D+1)).val by linarith)

lemma sqrt_mass (L : Side) : 1 ≤ Real.sqrt (L.val:ℝ) ∧ Real.sqrt (L.val:ℝ) ≤ L.val := by
  have he : 1 ≤ (L.val:ℝ) := by exact_mod_cast L.property
  exact ⟨Real.one_le_sqrt.mpr he, Real.sqrt_le_self_iff.mpr (Or.inr he)⟩

lemma pole_floor (p : Momentum) (hp : p ∈ baseCube) (M : Side) :
    meter.low^2*‖p‖^2 ≤ ‖divisor M p‖ := by
  apply le_trans _ (((divisor_real_bounds M (base_subset_realCube zone_pos hp)).1).trans (Complex.re_le_norm _))
  have hs : ‖p‖≤Real.sqrt (lengthSq p) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro a; apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f:=fun i : Axis => ‖p i‖ ^2) (fun i _ => by positivity) (Finset.mem_univ _)
  have hl : ‖p‖^2 ≤ lengthSq p := (pow_le_pow_left₀ (norm_nonneg _) hs _).trans_eq (Real.sq_sqrt (Finset.sum_nonneg (fun _ _=> sq_nonneg _)))
  gcongr
end YM.FormalBulk08.Flat
