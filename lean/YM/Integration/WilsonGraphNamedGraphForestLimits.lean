import YM.Integration.WilsonGraphPublicForestLimits
import YM.Integration.WilsonGraphGroupPositionReference

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonGraphNamedGraphForestLimits
open Filter
open WilsonGraphStandaloneCorrelation (Label)
open WilsonGraphPublicForestLimits (dimensional releasedAt)
open scoped Topology

/-- The group-only model reads the dimensionally released graph in the infrared limit. -/
theorem physical {g : YangMills.GaugeGroup} {n : ℕ} (a : Fin n → Label g)
    (x : YangMills.Points n) (hx : x ∈ YangMills.separated n) (k : ℕ) :
    (∀ ρ : ℝ, 0 < ρ →
      Tendsto (dimensional a x k ρ) YM.MS.Shine.dotty (𝓝 (releasedAt a x k ρ))) ∧
    Tendsto (releasedAt a x k) atTop
      (𝓝 ((_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation n k a x)) := by
  obtain ⟨atLength, infrared⟩ := WilsonGraphPublicForestLimits.physical a x hx k
  refine ⟨atLength, ?_⟩
  rw [WilsonGraphGroupPositionReference.agreement g n k a x hx]
  exact infrared

end YM.Integration.WilsonGraphNamedGraphForestLimits
end

