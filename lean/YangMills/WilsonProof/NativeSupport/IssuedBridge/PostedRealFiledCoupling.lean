import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedPhysicalConversionEntry
namespace IssuedBridge.PostedRealFiledCoupling
open YM YM.MS YM.MS.Land YM.MS.Fleet YM.FVA2 YM.FVA2.Register YM.FVA2.Scale
noncomputable section
variable {G : Gauge} (Z : WilsonPrescription G)
    (raw : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {S : Prescription (Press.portDeck G)} {simple : G.Simple} {dial : Bool}
    (matched : Main.Match Z simple raw S dial) (μ : ℝ)
def coefficient (k : ℕ) : ℝ := (PowerSeries.coeff k (Measure.f Z.criterion μ raw)).re
include matched in
theorem original :
    (∀ k, PowerSeries.coeff k (Measure.f Z.criterion μ raw) = (coefficient Z raw μ k : ℂ)) ∧
    coefficient Z raw μ 0 = 0 ∧ coefficient Z raw μ 1 = 1 := by
  let c := Measure.f Z.criterion μ raw
  have tangent := (matched.positionCoupling μ).1
  refine ⟨?_,?_,?_⟩
  · intro k
    have conjugate : (starRingEnd ℂ) (PowerSeries.coeff k c) = PowerSeries.coeff k c := by
      simpa only [PowerSeries.coeff_map] using (congrArg (PowerSeries.coeff k) tangent.real)
    have imaginary := congrArg Complex.im conjugate
    simp only [Complex.conj_im] at imaginary
    apply Complex.ext
    · rfl
    · change (PowerSeries.coeff k c).im = 0
      linarith
  · unfold coefficient
    rw [show PowerSeries.coeff 0 (Measure.f Z.criterion μ raw) = 0 from tangent.start]
    rfl
  · unfold coefficient
    rw [tangent.lead]
    rfl
end
end IssuedBridge.PostedRealFiledCoupling
