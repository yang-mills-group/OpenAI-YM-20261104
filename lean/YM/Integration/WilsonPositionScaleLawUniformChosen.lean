import YM.Integration.WilsonPositionScaleLawUniformIncome
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawUniformChosen
open Filter Set Function Metric Maxwell XSpace XSpace.Cirrus XSpace.Normalize FVA2 FVA2.Register
open Lattice Wilson RG Source Extraction Table Spec Climb PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS
open WilsonMaxwellThermometerKineticPanel WilsonPositionThermometerCapStation WilsonPositionCapTransport
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→tower S)(simple:G.Simple){Y:Ultrafilter (ℕ×ℕ)}
    (H:(Bel R.family.book).Hierarchy){arch:Trace.Terrace.Arch R.family}
local notation "visits" => trail.curry (Y : Filter (ℕ×ℕ))
open Trace.Terrace Trace.Over
theorem original (pace:WilsonWindowReportingPace.Slow R.kit)(bliss:Bliss F Y arch H)(lead:Leading F J)
    (paid:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (range:∀d:ℕ,∀c:ℝ,0<c→WilsonPhysicalPositionHalfRange.uniform J d c)
    {b:ℝ→ℝ}(center:TendC F (fun r=>J r 4) b)(heat:Coupling G (wilson arch)):
    WilsonPositionScaleLawUniformIncome.Bought F J simple (Y:=Y) H (arch:=arch):=by
  have therm:=WilsonPositionScaleLawTraceThermometer.original F J simple H pace bliss lead center
  refine ⟨b,⟨center,heat,?_⟩,therm,WilsonPositionScaleLawTraceTransport.original F J simple H therm,
    WilsonPositionScaleLawUniformTerminal.original F J simple H lead paid range therm,
    WilsonPositionScaleLawGuardNominated.original F J simple lead paid⟩
  intro window d up
  exact WilsonPositionScaleLawPhysicalClockTransfer.original F J simple lead center heat up
end YM.Integration.WilsonPositionScaleLawUniformChosen
end
