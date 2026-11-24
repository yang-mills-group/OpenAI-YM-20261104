import YM.Integration.FVA1Physical.Wilson.HotelTest
import YM.Integration.FVA1Physical.Sources.Round2.BareMarket
import YM.CommonPhysical.Plaquette
import YM.FullVolume.Finale.Program
import YM.Integration.FVA1Physical.Round2.CalibratedVoices
import YM.Integration.FVA1Physical.Round2.CircuitWilson
import YM.Integration.FVA1Physical.Wilson.AllOrdersSchur
import YM.Integration.FVA1Physical.Wilson.OrbitCumulants
import YM.Integration.FVA1Physical.Wilson.SchurRate

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk
open RGComparison.Core16 MSbar.Whisk MSbar.Rolling MSbar.Cacao Comparison.RG02 Push Push.Uniform SectorNext.Vacuum
open MSbar.Bakery.Portal MSbar.Mosaic
open scoped Classical Topology

private theorem ratio_unit {X : Type*} [MeasurableSpace X] (μ : Measure X) (ρ φ : X→ℝ)
    (positive : ∀ x,0≤ρ x) (bound : ∀ x,|φ x|≤1) :
    |(∫ x,ρ x*φ x ∂μ)/(∫ x,ρ x ∂μ)|≤1 := by
  by_cases hd : (∫ x,ρ x ∂μ)=0
  · rw [hd,div_zero,abs_zero];exact zero_le_one
  have den : Integrable ρ μ := by_contra (fun h=>hd (integral_undef h))
  have dpos : 0 < ∫ x,ρ x ∂μ := lt_of_le_of_ne (MeasureTheory.integral_nonneg positive) (Ne.symm hd)
  by_cases num : Integrable (fun x=>ρ x*φ x) μ
  · rw [abs_div,abs_of_pos dpos]
    apply (div_le_iff₀ dpos).mpr
    rw [one_mul]
    exact (norm_integral_le_integral_norm (fun x=>ρ x*φ x)).trans (integral_mono num.norm den fun x=>by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (positive x)]
      exact mul_le_of_le_one_right (positive x) (bound x))
  rw [integral_undef num,zero_div,abs_zero];exact zero_le_one

theorem expect_unit_any {G : Gauge} {c f : Side} {S : StepData c f} {R : Rep G f} (O : Config G c)
    {σ C δ Λ w : ℝ} (adm : Admitted O R S σ C δ Λ w) (φ : Config G f→ℝ) (unit : ∀ X,|φ X|≤1) :
    |expect S R O φ|≤1 := by
  unfold MSbar.Bulk.expect StepData.push
  simp only [Pi.mul_apply,smul_eq_mul]
  simpa only [mul_assoc,mul_comm (R.eval _) (φ _)] using
    (ratio_unit (prior G f) (fun x=>S.density R.beta x O * R.eval x) φ
      (fun x=>mul_nonneg (adm.kernel.positive x O) (adm.positive x)) unit)

end YM.Integration.FVA1Physical.Round2.Curvature
