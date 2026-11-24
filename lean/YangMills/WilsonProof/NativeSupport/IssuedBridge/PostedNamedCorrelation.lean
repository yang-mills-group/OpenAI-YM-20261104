import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFinitePinCorrelation
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedTranslatedExpansion

namespace IssuedBridge.PostedNamedCorrelation
open YangMills YangMills.Matching
open Filter Set MeasureTheory
open scoped Topology BigOperators Classical
noncomputable section

theorem original {g : GaugeGroup} {B : Maxwell.Reference g} (M : MSbar.Coefficients B)
    (A : Conversion B) {n m : ℕ} (a : Fin n → Label B) {clock : ℝ → ℝ}
    {actual : ℝ → Points n → ℂ} {old : ℕ → Points n → ℂ}
    (paid : HasExpansion m clock actual old)
    (agrees : ∀ k x, x ∈ WilsonFamily.separated n → old k x = A.correlation M k a x) :
    HasExpansion m clock actual (fun k x => A.correlation M k a x) := by
  have tested (φ : WilsonFamily.SeparatedTest n) (k : ℕ) :
      (fun x => φ x * old k x) = fun x => φ x * A.correlation M k a x := by
    funext x
    by_cases zero : φ x = 0
    · simp [zero]
    · rw [agrees k x (φ.tsupport_subset (subset_tsupport _ zero))]
  refine ⟨fun φ k => tested φ k ▸ paid.1 φ k,?_⟩
  intro K compact sep p ε eps
  filter_upwards [paid.2 K compact sep p ε eps] with r cost
  intro φ inside bound
  simpa only [← tested] using cost φ inside bound
end
end IssuedBridge.PostedNamedCorrelation
