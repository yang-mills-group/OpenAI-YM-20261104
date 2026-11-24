import YM.Integration.WilsonPositionScaleLawUniformGraduation
import YM.Integration.WilsonPositionScaleLawTraceTransport

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawUniformTerminal
open Filter Set Function Metric Maxwell XSpace XSpace.Cirrus XSpace.Normalize FVA2 FVA2.Register
open Lattice Wilson RG Source Extraction Table Spec Climb PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS
open WilsonMaxwellThermometerKineticPanel WilsonPositionThermometerCapStation WilsonPositionCapTransport
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→tower S)(simple:G.Simple){Y:Ultrafilter (ℕ×ℕ)}
    (H:(Bel R.family.book).Hierarchy){arch:Trace.Terrace.Arch R.family}
local notation "visits" => trail.curry (Y : Filter (ℕ×ℕ))
open MS MS.Land MS.Fleet MS.Book.Program FVA2.Arrival
def Published : Prop :=
  ∀(Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}, Main.Match Z simple M σ b →
  ∀(ν:ℝ)(A:ℝ→Group R.family 6){B:ℕ}, 0<B → Book (f:=f) (l:=Y) (H:=H) A J →
  ∀(axis:ℝ×(ℕ×ℕ)→ℝ), (∀ᶠw in visits, 0<axis w) →
    Tendsto (fun w=>WilsonPositionRawCutoff.thermometer Z F J A w.1 w.2/axis w) visits (𝓝 1) →
    Tendsto (fun w=>axis w/WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=B) w.1 w.2) visits (𝓝 1) →
      ∀d:ℕ,WilsonPositionScaleLawUniformGraduation.Output Z M ν F J d

theorem original (lead:Leading F J)(paid:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (range:∀d:ℕ,∀c:ℝ,0<c→WilsonPhysicalPositionHalfRange.uniform J d c)
    {bias:ℝ→ℝ}(clock:WilsonPositionScaleLawTraceThermometer.Every F J simple (Y:=Y) H (arch:=arch) bias):
    Published F J simple (Y:=Y) H := by
  intro Z M σ b model ν A B hB book axis live panel dates d
  exact WilsonPositionScaleLawUniformGraduation.original Z M model ν F J lead paid
    (clock Z A hB book axis live panel dates).2.1 range d
end YM.Integration.WilsonPositionScaleLawUniformTerminal
end
