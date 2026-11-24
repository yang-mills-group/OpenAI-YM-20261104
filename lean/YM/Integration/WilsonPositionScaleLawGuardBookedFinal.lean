import YM.Integration.WilsonPositionScaleLawGuardBooked
import YM.Integration.WilsonPositionScaleLawGuardFieldStep
import YM.Integration.WilsonPositionScaleLawGuardTopStep
import YM.Integration.WilsonPositionScaleLawGuardDescent

/-! Full fixed-field evolution from one original mixed book and the measured signed field and clock orders on that same preappointed physical course. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardBookedFinal
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open Lattice Wilson RG Source RG17 WilsonPositionThermometerCapStation
open WilsonPositionScaleLawWindow (RangeSpec)
open WilsonPositionScaleLawClock (radius)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawBooked (filed)
open scoped Topology Classical Asymptotics
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{Y:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T B:ℕ}{δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→WilsonOriginalTwoFlatPublicBooks.Book F (l:=ℓ) Y arch D T s.val)
    (A:ℝ→Group R.family 6)
local notation "visits"=>trail.curry (ℓ:Filter (ℕ×ℕ))
local notation "therm"=>WilsonPositionRawCutoff.thermometer Z F J A
local notation "gcut"=>WilsonPositionThermometerSevenFaceRate.temperature (R:=R) hG (B:=B)

local instance half:RangeSpec:=⟨1/2,by norm_num⟩
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawGuardLittle (scale)


open WilsonPositionScaleLawGuardBooked (fieldPaid)
open WilsonPositionScaleLawGuardTopStep (column)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawGuardPhysical (expected)
open WilsonPositionScaleLawGrade (grade)

def full (d:ℕ):Prop:=(∀q,scale F J Z M ν d q) ∧
    (∀q:ℕ,∀O:S.Field d,(fun r=>physical F J Z d r O-grade R.family (Fin.last d) (physical F J Z d r O))=o[trail] (fun r=>kinetic Z F J r^q)) ∧
    ∃p:ℕ,∀q:ℕ,∀O:S.Field d,(fun w:ℝ×Ratio=>physical F J Z d w.1 O-
      expected F J Z M ν d (q+2*p) w.1 w.2 (physical F J Z d (w.2.val*w.1) O))=o[sweep] (fun w=>kinetic Z F J w.1^q)

def finite (d:ℕ):Prop:=∃p:ℕ,∀q Q:ℕ,q+2*p≤Q→fieldPaid Z M ν F J d Q→WilsonPositionScaleLawThermometerScale.Earned Z M ν F J Q→
    ∀O:S.Field d,(fun w:ℝ×Ratio=>column Z F J d w.1 O-
      expected F J Z M ν d (q+2*p) w.1 w.2 (column Z F J d (w.2.val*w.1) O))=o[sweep] (fun w=>kinetic Z F J w.1^q)

include H in
theorem original (bliss:Bliss F ℓ arch Y)(slow:WilsonWindowReportingPace.Slow R.kit)
    (δp:0<δ)(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)(lead:Leading F J)
    (paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(k:Fin (D+1))(six:6≤k.val)(avoid:Finset E4)
    (hB:0<B)(book:WilsonPositionCapTransport.Book (f:=f) (l:=ℓ) (H:=Y) A J)
    (axis:ℝ×(ℕ×ℕ)→ℝ)(live:∀ᶠw in visits,0<axis w)
    (measured:Tendsto (fun w=>therm w.1 w.2/axis w) visits (𝓝 1))
    (dates:Tendsto (fun w=>axis w/gcut w.1 w.2) visits (𝓝 1)):
    ∃v:(Bel R.family.book).Field k.val,WilsonPhysicalPositionAdmissible.real R.family k.val v=v ∧ ∃a:ℝ,0<a ∧
      (filed F J books k avoid v a→∀d≤k.val,
        (fieldPaid Z M ν F J d 2→WilsonPositionScaleLawThermometerScale.Earned Z M ν F J 2→finite Z M ν F J d) ∧
        ((∀q,2≤q→fieldPaid Z M ν F J d q)→(∀q,2≤q→WilsonPositionScaleLawThermometerScale.Earned Z M ν F J q)→full Z M ν F J d)):=by
  obtain ⟨v,hv,a,ha,read⟩:=WilsonPositionScaleLawGuardBooked.original Z M H ν F J books A bliss slow δp below lead paid k six avoid hB book axis live measured dates
  have funded:Coupling G (kinetic Z F J):=(WilsonMaxwellThermometerKineticRunning.original Z F J A hG slow hB bliss book lead axis live measured dates).2
  refine ⟨v,hv,a,ha,?_⟩;intro vote d hd
  have sold:=(read vote).1 d hd
  constructor
  · intro fee clock
    obtain ⟨p,steps⟩:=WilsonPositionScaleLawGuardTopStep.original Z M H ν F J d funded (sold 2 fee clock)
    refine ⟨p,?_⟩;intro q Q lower fields clock
    exact steps q (WilsonPositionScaleLawGuardDescent.original Z M H ν F J funded d lower (sold Q fields clock))
  · intro fields clocks
    have positive (q:ℕ)(large:2≤q):scale F J Z M ν d q:=sold q (fields q large) (clocks q large)
    have all (q:ℕ):scale F J Z M ν d q:=by
      by_cases high:2≤q
      · exact positive q high
      · exact WilsonPositionScaleLawGuardDescent.original Z M H ν F J funded d (by omega : q≤2) (positive 2 le_rfl)
    exact ⟨all,WilsonPositionScaleLawGuardOffGrade.original Z M H ν F J d funded all,WilsonPositionScaleLawGuardFieldStep.original Z M H ν F J d funded all⟩

end YM.Integration.WilsonPositionScaleLawGuardBookedFinal
end
