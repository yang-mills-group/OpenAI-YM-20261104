import YM.Integration.WilsonConditionalTaylorThermalOnsite
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! A finite-field fourth-order remainder for the original Haar density
on one bond. Its radius and price do not depend on the torus or descent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalLocalHaar
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open PertExtension PertExtension.Series Tested Radial WilsonConditionalTaylorThermalOnsite
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} (P : ChartRatio G) (R : LocalRatio P)

def relative (z : G.Color) := Chart.fee P z/P.scale-1

include R

theorem anchor : Chart.fee P 0=P.scale := by
  rw [Chart.fee,R.anchored,mul_one,max_eq_left R.scale.le]

theorem ratio : ∃δ C:ℝ,0<δ ∧ 0≤C ∧ ∀z:G.Color,‖z‖≤δ→
    |relative P z-quadratic P z|≤C*‖z‖^4 := by
  have sm : ContDiffAt ℝ ∞ (Chart.fee P) 0 := (Chart.Ratio.fee_smooth R).of_le (by simp)
  obtain ⟨δ,C,hδ,hC,bill⟩ := deposition (Chart.fee P) 3 sm
  refine ⟨δ,C/P.scale,hδ,div_nonneg hC R.scale.le,?_⟩
  intro z hz
  have odd (k : ℕ) (h : Odd k) := WilsonConditionalTaylorThermalHaarOdd.diagonal sm
    (WilsonConditionalTaylorThermalHaarOdd.mirror P R) h z
  have b := bill z 1 one_pos (by simpa using hz)
  have first := odd 1 (by decide)
  have third := odd 3 (by decide)
  have amount : |Chart.fee P z-(P.scale+jet (Chart.fee P) 2 z)|≤C*‖z‖^4 := by
    simpa [Zone.eval,Finset.sum_range_succ,first,third,anchor P R,Real.norm_eq_abs] using b
  have sign : relative P z-quadratic P z=(Chart.fee P z-(P.scale+jet (Chart.fee P) 2 z))/P.scale := by
    unfold relative WilsonConditionalTaylorThermalOnsite.quadratic;field_simp [R.scale.ne'];ring
  rw [sign,abs_div,abs_of_pos R.scale]
  exact (div_le_div_of_nonneg_right amount R.scale.le).trans_eq (by ring)

omit R in
theorem basic {x:ℝ} (small : |x|≤1/2) : |Real.log (1+x)-x|≤2*|x|^2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x:=-x) (by rw [abs_neg];linarith) 1
  have s : |Real.log (1+x)-x|≤|x|^2/(1-|x|) := by
    simpa [sub_eq_add_neg,add_comm] using h
  refine s.trans ((div_le_iff₀ (by linarith)).mpr ?_)
  nlinarith [mul_nonneg (sq_nonneg |x|) (show 0≤1/2-|x| by linarith)]

theorem original : ∃δ C:ℝ,0<δ ∧ 0≤C ∧ ∀z:G.Color,‖z‖≤δ→
    0<Chart.fee P z ∧ |Real.log (Chart.fee P z/P.scale)-quadratic P z|≤C*‖z‖^4 := by
  obtain ⟨ρ,B,hr,hB,remainder⟩:=ratio P R
  have sm : ContinuousAt (relative P) 0 :=
    ((Chart.Ratio.fee_smooth R).continuousAt.div_const _).sub continuousAt_const
  have near : ∀ᶠx in 𝓝 (0:G.Color), |relative P x|<1/2 :=
    sm.abs.tendsto.eventually (eventually_lt_nhds (by simp [relative,anchor P R,R.scale.ne']))
  obtain ⟨v,hv,inBall⟩:=Metric.mem_nhds_iff.mp near
  let u := B+price P
  refine ⟨min ρ (min 1 (v/2)),2*u^2+B,lt_min hr (lt_min one_pos (by linarith)),by positivity,?_⟩
  intro z hz
  have hρ := hz.trans (min_le_left ..)
  have h1 := (hz.trans (min_le_right ..)).trans (min_le_left ..)
  have hv' : ‖z‖<v := lt_of_le_of_lt ((hz.trans (min_le_right ..)).trans (min_le_right ..)) (by linarith)
  have small : |relative P z|<1/2 := inBall (by simpa [Metric.mem_ball,dist_zero_right] using hv')
  have zin : 0<1+relative P z := by linarith [(neg_le_abs (relative P z))]
  have reset : 1+relative P z=Chart.fee P z/P.scale := by unfold relative;ring
  refine ⟨(div_pos_iff_of_pos_right R.scale).mp (reset ▸ zin),?_⟩
  have z4 : ‖z‖^4≤‖z‖^2 := by
    have p : ‖z‖^2≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0≤1+‖z‖ by positivity)]
    nlinarith [mul_nonneg (sq_nonneg ‖z‖) (sub_nonneg.mpr p)]
  have est : |relative P z|≤u*‖z‖^2 := calc
    _ ≤ |relative P z-quadratic P z|+|quadratic P z| := by
      simpa using (abs_add_le (relative P z-quadratic P z) (quadratic P z))
    _ ≤ B*‖z‖^4+price P*‖z‖^2 := add_le_add (remainder z hρ) (bound P R z)
    _ ≤ _ := by
      change _≤(B+price P)*‖z‖^2
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left z4 hB) le_rfl
  have square := pow_le_pow_left₀ (abs_nonneg _) est 2
  rw [←reset]
  calc
    _ ≤ |Real.log (1+relative P z)-relative P z|+|relative P z-quadratic P z| := by
      simpa using (abs_add_le (Real.log (1+relative P z)-relative P z) (relative P z-quadratic P z))
    _ ≤ 2*|relative P z|^2+B*‖z‖^4 := add_le_add (basic small.le) (remainder z hρ)
    _ ≤ 2*(u*‖z‖^2)^2+B*‖z‖^4 := add_le_add (mul_le_mul_of_nonneg_left square (by norm_num)) le_rfl
    _ = _ := by ring

end YM.Integration.WilsonConditionalTaylorThermalLocalHaar
