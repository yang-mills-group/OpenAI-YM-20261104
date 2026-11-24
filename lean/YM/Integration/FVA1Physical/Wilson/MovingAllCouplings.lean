import YM.Integration.FVA1Physical.Wilson.MovingMarked
import YM.Integration.FVA1Physical.Wilson.MovingEnvelope

/-! Extend the fixed-torus graded estimate from small positive coupling to
every positive coupling, including the coupling measured by the actual run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set Function Metric Lattice RG YM.Wilson Tree Precision
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Chart
open PertExtension.Series PertExtension.Series.Tested FormalOPE.RG10.MultiGauge FVA2.CityHistory
open Comparison.RG02
open scoped Classical Topology
variable {G : Gauge} {n c : Side} (d : Descent n c)

theorem all_coupling_price {Z : ChartRatio G} (hZ : LocalRatio Z) (h : d.Room G)
    (t : d.Tags) (u : Pins G c) (a : ℕ → ℝ) (O : Config G n → ℝ)
    (hO : Continuous O) (hI : GaugeInvariant O) {w : ℕ}
    (hw : Assembly.GradeAt w (O ∘ expLinks G (Edge (Site n)))) (r : ℕ) :
    let k := fun j => PowerSeries.coeff (w+j) (Stack.read u (skyread Z d t h (Delay.stones a) (exPay O)))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ, 0 < g →
      ‖g⁻¹^w • d.conditioned (offset a g) O (expLinks G _ (g • u)) - peval k r g‖ ≤ C*g^(r+1) := by
  intro k
  apply positive_price (physical_ray_graded d hZ h t u a O hO hI hw) _ r
  intro s hs
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn (s:=univ) hO.continuousOn
  refine ⟨s⁻¹^w*|M|,mul_nonneg (pow_nonneg (inv_nonneg.mpr hs.le) _) (abs_nonneg _),?_⟩
  intro g H
  have hg := hs.trans_le H
  rw [norm_smul,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hg.le) _)]
  exact mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr hg.le) ((inv_le_inv₀ hg hs).mpr H) _)
    (conditioned_bound (room_ok d h) _ (fun i => (hM i (mem_univ _)).trans (le_abs_self _)) hO _)
    (norm_nonneg _) (pow_nonneg (inv_nonneg.mpr hs.le) _)

end YM.Integration.FVA1Physical.Wilson
