import YM.Integration.WilsonEmittedNestedSelection
import YM.Integration.WilsonOriginalBlissDressedField
import YM.Integration.WilsonPositionProgramArithmeticRegistered

/-! Pin the prescription before all finite position measurements. At any of
its actual booked reporters, the same original Wilson field and extraction
filter price the signed dressed-Q error. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissRegisteredResponse
open Filter Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl OPE.Therm
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.FVAAlt2
open WilsonPositionProgramReporterBand
open XSpace XSpace.Cirrus FVA2 FVA2.Register MS MS.Land
open Extraction Extraction.Banks RG17 Spec Table
open scoped Classical ENNReal BigOperators

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {H:(Climb.Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}
  {arch:Trace.Terrace.Arch R.family}(bliss:Trace.Pilot.Bliss F l arch H)
  (J:ℝ→PhysMS.tower S)(level:ℝ→ℕ)
  (shift:∀ d,ℝ→R.family.label d ≃ₗ[ℂ] R.family.label d)
  (Y:Poetry R.family.path.levels)(simple:G.Simple)

private def statement {p:Prop} (_:p):Prop:=p

/-- The original formal inscription and the physical assay share every index
of the same selected reporter sequence. The signed estimate is uniform over
all requested physical fields at their own fixed reference. -/
def Measured {D:XSpace.Run}(Q:Prescription (Press.portDeck G))
    {filed:∀stage,Band R D stage → Prop} (_:∃stage,∃T:Band R D stage,filed stage T):Prop:=
  ∃stage,∃T:Band R D stage,filed stage T ∧ ∀(h:ℕ)(fee:ℝ)(pos:0≤fee),
    statement (WilsonOriginalBlissDressedField.original R Q h F bliss J level shift T Y simple fee pos)

theorem original {AUX:Type}{a:Axis}{ε:ℝ}
    (schedule:WilsonEmittedNestedGround.Schedule R)(slow:WilsonWindowReportingPace.Slow R.kit)
    (branch:∀P:RG.Patch,P.Branches R.family.path.levels.clock.kernel G)
    (Z:WilsonPrescription G){M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {originalQ:Prescription (Press.portDeck G)}{dial:Bool}
    (matchMS:Main.Match Z simple M originalQ dial):
    ∃Q:Prescription (Press.portDeck G),
      ∃calibration:TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR R) (Press.portDeck G)) Q,
      ∀(p:ℕ)(color:G.ColorIndex)(floor:ℕ){d₀:ℕ}(hd:0<d₀)(ratio:Z.run.ratio=(3:ℕ)^d₀)
        {n:ℕ}(nonempty:0<n)(K:Set (Points n))(compact:IsCompact K)(apart:K⊆conf n),
      Measured R F bliss J level shift Y simple Q
        (WilsonPositionProgramArithmeticPinnedPrescription.original (AUX:=AUX) R
          (a:=a) (ε:=ε) schedule.1 schedule.2 slow branch p color Z matchMS Q calibration
          floor hd ratio slow.2 nonempty K compact apart):=by
  obtain ⟨Q,calibration⟩:=High_stopsPl simple M (YM.FVAAlt2.Lobby.Table (Lodge.basisR R) (Press.portDeck G))
  refine ⟨Q,calibration,?_⟩
  intro p color floor d₀ hd ratio n nonempty K compact apart
  obtain ⟨stage,T,program⟩:=WilsonPositionProgramArithmeticPinnedPrescription.original (AUX:=AUX)
    R (a:=a) (ε:=ε) schedule.1 schedule.2 slow branch p color Z matchMS Q calibration
    floor hd ratio slow.2 nonempty K compact apart
  exact ⟨stage,T,program,fun h fee pos=>WilsonOriginalBlissDressedField.original R Q h F bliss J level shift T Y simple fee pos⟩

end YM.Integration.WilsonOriginalBlissRegisteredResponse
