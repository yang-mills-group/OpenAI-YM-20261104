import YM.Integration.FVA1Physical.Wilson.MovingConditional

/-! The inherited origin-normalized vacuum retains its nonflat Gaussian
action. The chart determinant and tag priors are calculated before the
normalization, and cancel across the two retained fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function PowerSeries MeasureTheory Lattice RG YM.Wilson Tree Precision
open RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots FormalOPE.RG10.MultiGauge
open FVA2 FVA2.CityHistory FVA2.RayScatter
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c) (Z : ChartRatio G) (t : d.Tags)
    (h : d.Room G) (a : ℕ → ℝ) (u : Pins G c)

def rayGaussian : ℝ := Real.exp (-(retained d t h).flourish u / 2)

def centeredRay : PowerSeries ℝ :=
  let A := μLedger d Z t h (Delay.stones a)
  C (rayGaussian d t h u) * Stack.read u A * (Stack.read 0 A)⁻¹

theorem rayGaussian_zero : rayGaussian d t h (0 : Pins G c) = 1 := by
  simp [rayGaussian,Quadratic.flourish]

private theorem factor_moves (s : d.Tags) :
    rayFactor d Z s u h = rayGaussian d t h u * rayFactor d Z s 0 h := by
  rw [rayGaussian,← pure_t d s t h]
  unfold rayFactor basePower
  change Real.exp (-1-(retained d s h).flourish u/2)*_ * _ =
    Real.exp (-(retained d s h).flourish u/2) * (Real.exp (-1-(retained d s h).flourish 0/2)*_ * _)
  rw [show (retained d s h).flourish 0 = 0 by simp [Quadratic.flourish],zero_div,sub_zero,
    show -1-(retained d s h).flourish u/2 = -(retained d s h).flourish u/2 + (-1) by ring,Real.exp_add]
  ring

theorem ray_den_constant (hZ : LocalRatio Z) :
    constantCoeff (Stack.read u (μLedger d Z t h (Delay.stones a))) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply,Stack.reading_term,coeff_zero_eq_constantCoeff_apply,
    marketZ d Z t h (Delay.stones a) hZ]
  rfl

theorem ray_bank_absolute (hZ : LocalRatio Z) :
    mk (rayBank d Z u a 1) =
    C (∑ s, rayFactor d Z s 0 h) * (C (rayGaussian d t h u) *
      Stack.read u (μLedger d Z t h (Delay.stones a))) := by
  have he : mk (rayBank d Z u a 1) = ∑ s, mk (rayCoefficient d Z a s u 1) := by
    apply PowerSeries.ext; intro j
    simp [rayBank,Finset.sum_apply]
  rw [he,map_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [ray_ticket d Z s u (W:=1) contDiffAt_const hZ h a,
    share_part d s (Delay.stones a) h _ Z hZ, Stack.rise_one,mul_one]
  change C (rayFactor d Z s u h) * Stack.read u (μLedger d Z s h (Delay.stones a)) = _
  rw [sameFieldDen Z d s t (Delay.stones a) h,factor_moves d Z t h u s,map_mul]
  ring

include t h in
theorem ray_origin_positive (hZ : LocalRatio Z) : 0 < rayBank d Z 0 a 1 0 := by
  have hmass := Finset.sum_pos (fun s _ => rayFactor_pos d Z s 0 hZ h) Finset.univ_nonempty
  rw [← coeff_mk 0 (rayBank d Z 0 a 1), coeff_zero_eq_constantCoeff_apply,
    ray_bank_absolute d Z t h a 0 hZ, rayGaussian_zero, map_one,one_mul,
    map_mul, constantCoeff_C, ray_den_constant d Z t h a 0 hZ,mul_one]
  exact hmass

theorem centered_ray_quotient (hZ : LocalRatio Z) : centeredRay d Z t h a u =
    mk (rayBank d Z u a 1) * (mk (rayBank d Z 0 a 1))⁻¹ := by
  let V := μLedger d Z t h (Delay.stones a)
  have hb : constantCoeff (mk (rayBank d Z 0 a 1)) ≠ 0 := by
    simpa only [constantCoeff_mk] using (ray_origin_positive d Z t h a hZ).ne'
  have hv : constantCoeff (Stack.read 0 V) ≠ 0 :=
    (ray_den_constant d Z t h a 0 hZ).trans_ne one_ne_zero
  apply (eq_mul_inv_iff_mul_eq hb).mpr
  rw [ray_bank_absolute d Z t h a 0 hZ,rayGaussian_zero,map_one,one_mul,ray_bank_absolute d Z t h a u hZ]
  change (C _ * Stack.read u V * (Stack.read 0 V)⁻¹) * (C _ * Stack.read 0 V) = _
  have pay := PowerSeries.mul_inv_cancel (Stack.read 0 V) hv
  calc
    _ = (C (∑ s, rayFactor d Z s 0 h) * (C (rayGaussian d t h u) * Stack.read u V)) *
        (Stack.read 0 V * (Stack.read 0 V)⁻¹) := by ring
    _ = _ := by rw [pay,mul_one]

theorem centered_ray_lead (hZ : LocalRatio Z) :
    constantCoeff (centeredRay d Z t h a u) = rayGaussian d t h u := by
  let A := μLedger d Z t h (Delay.stones a)
  have hv : constantCoeff (Stack.read 0 A) ≠ 0 :=
    (ray_den_constant d Z t h a 0 hZ).trans_ne one_ne_zero
  have hi := congrArg (constantCoeff (R:=ℝ)) (PowerSeries.mul_inv_cancel (Stack.read 0 A) hv)
  rw [map_mul,ray_den_constant d Z t h a 0 hZ,one_mul,map_one] at hi
  rw [centeredRay,map_mul,map_mul,constantCoeff_C,ray_den_constant d Z t h a u hZ,mul_one,hi,mul_one]

end YM.Integration.FVA1Physical.Wilson
