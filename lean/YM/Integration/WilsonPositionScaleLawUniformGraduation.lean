import YM.Integration.WilsonPositionScaleLawGuardBookedCofinal

/-! Kinetic and fixed-field scale on one actually uniform original frame at every grade. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawUniformGraduation
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
    {Y:(Bel R.family.book).Hierarchy}
local instance half:RangeSpec:=⟨1/2,by norm_num⟩
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawGuardLittle (scale)
open WilsonPositionScaleLawGuardBooked (fieldPaid)
open WilsonPositionScaleLawGuardBookedFinal (finite full)
open WilsonPhysicalPositionHalfRange (uniform)
def Output (d:ℕ):Prop:=
    (∀q:ℕ,fieldPaid Z M ν F J d q→WilsonPositionScaleLawThermometerScale.Earned Z M ν F J q→scale F J Z M ν d q) ∧
    (fieldPaid Z M ν F J d 1→scale F J Z M ν d 1) ∧
    (∀Q:ℕ,2≤Q→fieldPaid Z M ν F J d Q→WilsonPositionScaleLawThermometerScale.Earned Z M ν F J Q→finite Z M ν F J d) ∧
      ((∀n:ℕ,∃Q:ℕ,n≤Q ∧ fieldPaid Z M ν F J d Q ∧ WilsonPositionScaleLawThermometerScale.Earned Z M ν F J Q)→full Z M ν F J d)

include H in
theorem original (lead:Leading F J)(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (funded:Coupling G (kinetic Z F J))(range:∀d:ℕ,∀c:ℝ,0<c→uniform J d c) (d:ℕ):Output Z M ν F J d:=by
  have raw (j:ℕ):WilsonPositionScaleLawCompactBranch.Raw J j :=
    WilsonPositionScaleLawBooked.raw J j (range j (1/2) (by norm_num))
  have sold (q:ℕ) (fields:fieldPaid Z M ν F J d q)(clock:WilsonPositionScaleLawThermometerScale.Earned Z M ν F J q):
      scale F J Z M ν d q:=WilsonPositionScaleLawGuardLittle.original F J Z M H ν lead paid funded d q (raw d) (raw 6) fields clock
  refine ⟨sold,?_,?_,?_⟩
  · intro fields
    apply WilsonPositionScaleLawGuardLittle.measured F J Z M H ν lead paid funded d 1
    · exact WilsonPositionScaleLawQinter.qinter Z M H ν F J lead paid d 1 (raw d) fields
    · have speed:(fun z:ℝ×Ratio=>kinetic Z F J (z.2.val*z.1)-kinetic Z F J z.1)=o[sweep] (fun z:ℝ×Ratio=>kinetic Z F J z.1):=
        WilsonPositionScaleLawKineticRatio.first (W:=half) hG funded
      simpa only [WilsonPositionScaleLawBookedFirst.printed Z M H ν F J,Complex.ofReal_re,pow_one] using speed
  · intro Q large fields clock
    have two:=WilsonPositionScaleLawGuardDescent.original Z M H ν F J funded d large (sold Q fields clock)
    obtain ⟨p,steps⟩:=WilsonPositionScaleLawGuardTopStep.original Z M H ν F J d funded two
    refine ⟨p,?_⟩;intro q n lower fare tick
    exact steps q (WilsonPositionScaleLawGuardDescent.original Z M H ν F J funded d lower (sold n fare tick))
  · intro cofinal
    have all (q:ℕ):scale F J Z M ν d q:=by
      obtain ⟨Q,hQ,fields,clock⟩:=cofinal q
      exact WilsonPositionScaleLawGuardDescent.original Z M H ν F J funded d hQ (sold Q fields clock)
    exact ⟨all,WilsonPositionScaleLawGuardOffGrade.original Z M H ν F J d funded all,
      WilsonPositionScaleLawGuardFieldStep.original Z M H ν F J d funded all⟩
end YM.Integration.WilsonPositionScaleLawUniformGraduation
end
