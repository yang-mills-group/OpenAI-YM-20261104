import YM.Integration.WilsonThermometerCompulsoryReturn

/-! Hear a bounded Borel insertion against the full earlier original Wilson law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerEarlierHearing
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology
open WilsonThermometerCourseHearing
open WilsonThermometerCompulsoryReturn
open private earlier from YM.Integration.WilsonThermometerCompulsoryReturn
variable {G : Gauge} (R : Run G)

theorem original {j p top : ℕ} (atDate : j ≤ top)
    {f : Config G (R.family.side j p) → ℂ} {cap : ℝ}
    (borel : Measurable f) (bound : ∀ F, ‖f F‖ ≤ cap) : Heard R (top:=top) f cap :=
  earlier R atDate borel bound

end YM.Integration.WilsonThermometerEarlierHearing
end
