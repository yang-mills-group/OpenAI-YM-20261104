import YM.Integration.WilsonCloseCaptureDate

/-! The two compact support filings use one coarse radius and one fine mesh
on the same actual date and cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstRoseGeometry
open Function Filter Lattice
open scoped Topology

structure Fits (S:Schedule)(c r:ℝ)(m f:ℕ):Prop where
  small : c*r ≤ S.a 0
  older : m+1 ≤ WilsonCloseCaptureDate.level S (c*r)
  finer : WilsonCloseCaptureDate.level S (c*r) ≤ f
  margin : 8*S.a f < S.a (WilsonCloseCaptureDate.level S (c*r))

private theorem one (S:Schedule){c r:ℝ}(cp:0 < c)(rp:0 < r){m f:ℕ}
    (outside:c*r ≤ S.a (m+1))(inside:8*S.a f < c*r):Fits S c r m f:=by
  have small: c*r ≤ S.a 0:=outside.trans (S.strictAnti.antitone (Nat.zero_le _))
  obtain ⟨step,coarse⟩:=WilsonCloseCaptureDate.bracket S (mul_pos cp rp) small
  have af:S.a f < c*r:=by linarith only [inside,S.a_pos f]
  refine ⟨small,?_,?_,inside.trans_le coarse⟩
  · by_contra! bad
    exact (not_lt_of_ge (outside.trans (S.strictAnti.antitone (Nat.succ_le_of_lt bad)))) step
  · by_contra! bad
    exact (not_lt_of_ge coarse) ((S.strictAnti bad).trans af)

theorem original (S:Schedule){c h r:ℝ}(cp:0 < c)(hp:0 < h)(rp:0 < r){m f:ℕ}
    (outside:max c h*r ≤ S.a (m+1))(inside:8*S.a f < min c h*r):
    Fits S c r m f ∧ Fits S h r m f:=
  ⟨one S cp rp ((mul_le_mul_of_nonneg_right (le_max_left ..) rp.le).trans outside)
      (inside.trans_le (mul_le_mul_of_nonneg_right (min_le_left ..) rp.le)),
   one S hp rp ((mul_le_mul_of_nonneg_right (le_max_right ..) rp.le).trans outside)
      (inside.trans_le (mul_le_mul_of_nonneg_right (min_le_right ..) rp.le))⟩

theorem eventually {α:Type*}(S:Schedule)(l:Filter α){r:α → ℝ}{m f:α → ℕ}
    (rp:∀ᶠ x in l,0 < r x)(outer:Tendsto (fun x=>r x/S.a (m x+1)) l (𝓝 0))
    (fine:Tendsto (fun x=>S.a (f x)/r x) l (𝓝 0)){c h:ℝ}(cp:0 < c)(hp:0 < h):
    ∀ᶠ x in l,Fits S c (r x) (m x) (f x) ∧ Fits S h (r x) (m x) (f x):=by
  have big:0 < max c h:=cp.trans_le (le_max_left ..)
  have little:0 < min c h:=lt_min cp hp
  filter_upwards [rp,outer.eventually_lt_const (inv_pos.mpr big),
    fine.eventually_lt_const (div_pos little (by norm_num:0 < (8:ℝ)))] with x pos before after
  apply original S cp hp pos
  · have z: r x < (max c h)⁻¹*S.a (m x+1):=(div_lt_iff₀ (S.a_pos _)).mp before
    have t:=mul_le_mul_of_nonneg_left z.le big.le
    simpa only [←mul_assoc,mul_inv_cancel₀ big.ne',one_mul] using t
  · have z:S.a (f x) < (min c h/8)*r x:=(div_lt_iff₀ pos).mp after
    linarith only [z]

end YM.Integration.WilsonAddressedPublicFirstRoseGeometry
end
