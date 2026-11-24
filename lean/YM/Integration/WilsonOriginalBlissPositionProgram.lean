import YM.Integration.WilsonOriginalBlissFundedResponse
import YM.Integration.WilsonSubcriticalOriginalProgram

/-! Joint compact-position inscription on the physical extraction.
The nominated auxiliary geometry, matched MS frame and calibrated truncation
bank remain fixed before all finite orders and test supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissPositionProgram
open Filter Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl OPE.Therm
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.FVAAlt2
open WilsonPositionProgramReporterBand
open XSpace XSpace.Cirrus FVA2 FVA2.Register MS MS.Land
open Extraction Extraction.Banks RG17 Spec Table
open scoped Classical ENNReal BigOperators
universe u
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
  {H:(Climb.Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}
  {arch:Trace.Terrace.Arch R.family}(bliss:Trace.Pilot.Bliss F l arch H)
  (J:ℝ→PhysMS.tower S)(level:ℝ→ℕ)(shift:∀d,ℝ→R.family.label d ≃ₗ[ℂ] R.family.label d)
  {T₀:Campaign R}{W:Campaign.Pillars R T₀}{simple:G.Simple}{ε:ℝ}
  (fund:WilsonLimitConstruction.FundedOriginalProperties.{u} simple ε W)
  (schedule:WilsonEmittedNestedGround.Schedule R)(slow:WilsonWindowReportingPace.Slow R.kit)

def Book (AUX:Type)(axis:Axis)(Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (Q:Prescription (Press.portDeck G))
    (calibration:TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR R) (Press.portDeck G)) Q)
    {originalQ:Prescription (Press.portDeck G)}{dial:Bool}(matchMS:Main.Match Z simple M originalQ dial):Prop:=
    ∀(p:ℕ)(color:G.ColorIndex)(floor:ℕ){d₀:ℕ}(hd:0<d₀)(ratio:Z.run.ratio=(3:ℕ)^d₀)
      {n:ℕ}(nonempty:0<n)(K:Set (Points n))(compact:IsCompact K)(apart:K⊆conf n),
      WilsonOriginalBlissRegisteredResponse.Measured R F bliss J level shift
        fund.2.1.paid.stoves simple Q
        (WilsonPositionProgramArithmeticPinnedPrescription.original (AUX:=AUX) R
          (a:=axis) (ε:=ε) schedule.1 schedule.2 slow (WilsonOriginalBlissFundedResponse.branches R)
          p color Z matchMS Q calibration floor hd ratio slow.2 nonempty K compact apart)

/-- A previously named Wilson prescription and MS bank can enter this
same physical comparison without changing either one. -/
theorem filed {AUX:Type}(axis:Axis)(lead:PhysMS.Leading F J)(dial:Bool)
    (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))):
    ∃P:Prescription (Press.portDeck G), ∃pair:Main.Match Z simple M P dial,
      WilsonSubcriticalOriginalProgram.Compared F J Z M ∧ ∃Q:Prescription (Press.portDeck G),
      ∃calibration:TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR R) (Press.portDeck G)) Q,
        Book R F bliss J level shift fund schedule slow AUX axis Z M Q calibration pair:=by
  obtain ⟨P,pair,subcritical⟩:=WilsonSubcriticalOriginalProgram.genuine F J Z M simple lead dial
  obtain ⟨Q,calibration,program⟩:=WilsonOriginalBlissFundedResponse.original (AUX:=AUX) (a:=axis)
    R F bliss J level shift fund schedule slow Z pair
  exact ⟨P,pair,subcritical,Q,calibration,program⟩

/-- Right from the specified auxiliary geometric run, on the actual funded
Wilson field tower. The signed continuum subcritical comparison shares its
MS frame with the dressed-Q and finite chronological tests. -/
theorem original {AUX:Type}(axis:Axis)(lead:PhysMS.Leading F J)(dial:Bool)(L:XSpace.Run):
    ∃(Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (P:Prescription (Press.portDeck G)), Z.run=L ∧ ∃pair:Main.Match Z simple M P dial,
      WilsonSubcriticalOriginalProgram.Compared F J Z M ∧ ∃Q:Prescription (Press.portDeck G),
      ∃calibration:TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR R) (Press.portDeck G)) Q,
        Book R F bliss J level shift fund schedule slow AUX axis Z M Q calibration pair:=by
  obtain ⟨Z,M,P,geometry,pair,subcritical⟩:=WilsonSubcriticalOriginalProgram.original F J simple lead L dial
  obtain ⟨Q,calibration,program⟩:=WilsonOriginalBlissFundedResponse.original (AUX:=AUX) (a:=axis)
    R F bliss J level shift fund schedule slow Z pair
  exact ⟨Z,M,P,geometry,pair,subcritical,Q,calibration,program⟩

end YM.Integration.WilsonOriginalBlissPositionProgram
