import YM.Integration.WilsonPositionScaleLawGuardBookedFinal

/-! On the original chosen books, an unbounded set of jointly measured orders controls every physical order. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardBookedCofinal
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
        (∀Q:ℕ,2≤Q→fieldPaid Z M ν F J d Q→WilsonPositionScaleLawThermometerScale.Earned Z M ν F J Q→
          WilsonPositionScaleLawGuardBookedFinal.finite Z M ν F J d) ∧
        ((∀n:ℕ,∃Q:ℕ,n≤Q ∧ fieldPaid Z M ν F J d Q ∧ WilsonPositionScaleLawThermometerScale.Earned Z M ν F J Q)→
          WilsonPositionScaleLawGuardBookedFinal.full Z M ν F J d)):=by
  obtain ⟨v,hv,a,ha,read⟩:=WilsonPositionScaleLawGuardBooked.original Z M H ν F J books A bliss slow δp below lead paid k six avoid hB book axis live measured dates
  have funded:Coupling G (kinetic Z F J):=(WilsonMaxwellThermometerKineticRunning.original Z F J A hG slow hB bliss book lead axis live measured dates).2
  refine ⟨v,hv,a,ha,?_⟩;intro vote d hd
  have sold:=(read vote).1 d hd
  constructor
  · intro Q high fields clock
    have two:=WilsonPositionScaleLawGuardDescent.original Z M H ν F J funded d high (sold Q fields clock)
    obtain ⟨p,steps⟩:=WilsonPositionScaleLawGuardTopStep.original Z M H ν F J d funded two
    refine ⟨p,?_⟩;intro q n lower fare tick
    exact steps q (WilsonPositionScaleLawGuardDescent.original Z M H ν F J funded d lower (sold n fare tick))
  · intro cofinal
    have all (q:ℕ):scale F J Z M ν d q:=by
      obtain ⟨Q,hQ,field,clock⟩:=cofinal q
      exact WilsonPositionScaleLawGuardDescent.original Z M H ν F J funded d hQ (sold Q field clock)
    exact ⟨all,WilsonPositionScaleLawGuardOffGrade.original Z M H ν F J d funded all,
      WilsonPositionScaleLawGuardFieldStep.original Z M H ν F J d funded all⟩

end YM.Integration.WilsonPositionScaleLawGuardBookedCofinal
end
