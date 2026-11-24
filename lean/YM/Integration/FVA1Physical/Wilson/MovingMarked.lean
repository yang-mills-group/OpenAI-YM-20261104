import YM.Integration.FVA1Physical.Wilson.MovingPhysical

/-! Engineering shifts in the physical nonflat retained readout. A legitimate
incoming stencil has zero jets below its own grade. The full vacuum,
Gaussian uptake, and normalized FVA2 conditional preserve those zeros. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Lattice RG YM.Wilson Tree Precision RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MultiGauge
open FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MarkovChain.Warp FVA2 FVA2.CityHistory
open Comparison.RG02
open scoped Classical Topology ContDiff
variable {G : Gauge} {n c : Side} (d : Descent n c)

theorem physical_ray_graded {Z : ChartRatio G} (hZ : LocalRatio Z) (h : d.Room G)
    (t : d.Tags) (u : Pins G c) (a : ℕ → ℝ) (O : Config G n → ℝ)
    (hO : Continuous O) (hI : GaugeInvariant O) {w : ℕ}
    (hw : Assembly.GradeAt w (O ∘ expLinks G (Edge (Site n)))) :
    Aspiration (fun g : ℝ => g⁻¹^w • d.conditioned (offset a g) O (expLinks G _ (g • u)))
      (fun k => PowerSeries.coeff (w+k) (Stack.read u (skyread Z d t h (Delay.stones a) (exPay O)))) := by
  apply (physical_ray d u a hZ h t O hO hI hw.smooth).shift
  intro i hi
  have low : Through i (exPay O) 0 := by
    intro j hj
    apply Subtype.ext
    funext x
    change (PowerSeries.coeff j (Stack.rise _)).val x = _
    rw [← Stack.reading_term,Stack.read_rise]
    change Assembly.jet (O ∘ expLinks G _) j x = _
    rw [hw.jet_z x (hj.trans_lt hi),map_zero]
    rfl
  have placed : Through i (exValues d O) 0 := by
    simpa only [exValues,map_zero] using Shipment.boost_through (placement G d) low
  have result := enough Z hZ d h t (z:=Delay.stones a) (z':=Delay.stones a)
    (fun _ => Through.refl _) placed
  have zero : premiere d Z t h (Delay.stones a) 0 = 0 := by simp [premiere,Quadratic.fit]
  rw [zero] at result
  unfold term
  rw [Stack.reading_term,show skyread Z d t h (Delay.stones a) (exPay O) =
    premiere d Z t h (Delay.stones a) (exValues d O) from rfl,result i le_rfl,map_zero]
  rfl

end YM.Integration.FVA1Physical.Wilson
