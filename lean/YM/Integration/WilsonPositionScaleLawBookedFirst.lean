import YM.Integration.WilsonPositionScaleLawKineticRatio
import YM.Integration.WilsonPositionScaleLawThermometerScale
import YM.Integration.WilsonPositionScaleLawBookedPhysical

/-! The raw original measured kinetic account pays the first signed scale
coefficient on all positive compact ratio windows. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawBookedFirst
open Function Filter Set Finset Asymptotics Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open Lattice Wilson RG Source RG17 WilsonPositionThermometerCapStation
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawThermometerPay (target)
open scoped Topology Classical Asymptotics Polynomial
variable [W:RangeSpec]{G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{Y:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{B:ℕ}
    (A:ℝ→Group R.family 6)
local notation "visits"=>trail.curry (ℓ:Filter (ℕ×ℕ))
local notation "therm"=>WilsonPositionRawCutoff.thermometer Z F J A
local notation "gcut"=>WilsonPositionThermometerSevenFaceRate.temperature (R:=R) hG (B:=B)

include H in
theorem printed (z:ℝ×Ratio):target Z M ν F J 1 z=(kinetic Z F J z.1:ℂ):=by
  let s:=WilsonPositionScaleLawCompactIndependent.time z.2
  let p:=GroupS.ψ Z.criterion M ν s
  have x:coeff 0 p=0:=((H.details.normative ν).first.led s).start
  have y:coeff 1 p=1:=((H.details.normative ν).first.led s).lead
  change (trunc (1+1) p).eval (kinetic Z F J z.1:ℂ)=_
  rw [WilsonPositionScaleLawThermometerSmeared.paper,Finset.sum_range_succ,Finset.sum_range_succ,
    Finset.sum_range_zero,x,y];ring

include H in
theorem original (slow:WilsonWindowReportingPace.Slow R.kit)(hB:0<B)(bliss:Bliss F ℓ arch Y)
    (book:WilsonPositionCapTransport.Book (f:=f) (l:=ℓ) (H:=Y) A J)(lead:Leading F J)
    (axis:ℝ×(ℕ×ℕ)→ℝ)(live:∀ᶠw in visits,0<axis w)
    (measured:Tendsto (fun w=>therm w.1 w.2/axis w) visits (𝓝 1))
    (dates:Tendsto (fun w=>axis w/gcut w.1 w.2) visits (𝓝 1)):
    Tendsto (fun z:ℝ×Ratio=>kinetic Z F J (z.2.val*z.1)/kinetic Z F J z.1) sweep (𝓝 1) ∧
    (fun z:ℝ×Ratio=>kinetic Z F J (z.2.val*z.1)-(target Z M ν F J 1 z).re)=o[sweep] (fun z=>kinetic Z F J z.1^1):=by
  have funded:Coupling G (kinetic Z F J):=(WilsonMaxwellThermometerKineticRunning.original Z F J A hG slow hB bliss book lead axis live measured dates).2
  refine ⟨WilsonPositionScaleLawKineticRatio.signed hG funded,?_⟩
  simpa only [printed Z M H ν F J,Complex.ofReal_re,pow_one] using WilsonPositionScaleLawKineticRatio.first hG funded

end YM.Integration.WilsonPositionScaleLawBookedFirst
