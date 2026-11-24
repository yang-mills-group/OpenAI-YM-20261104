import YM.Integration.WilsonOriginalBlissRegisteredResponse

/-! Recover both input laws from the very original funded campaign
before calibrating its common position prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissFundedResponse
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

theorem branches : ∀P:RG.Patch,P.Branches R.family.path.levels.clock.kernel G := by
  rw [show R.family.path.levels.clock.kernel=R.metals.p.kernel from R.alloy.B.valid.kernel]
  exact R.metals.p.has

theorem original {AUX:Type}{a:Axis}
    (schedule:WilsonEmittedNestedGround.Schedule R)(slow:WilsonWindowReportingPace.Slow R.kit)
    (Z:WilsonPrescription G){M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {originalQ:Prescription (Press.portDeck G)}{dial:Bool}
    (matchMS:Main.Match Z simple M originalQ dial):
    ∃Q:Prescription (Press.portDeck G),
      ∃calibration:TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR R) (Press.portDeck G)) Q,
      ∀(p:ℕ)(color:G.ColorIndex)(floor:ℕ){d₀:ℕ}(hd:0<d₀)(ratio:Z.run.ratio=(3:ℕ)^d₀)
        {n:ℕ}(nonempty:0<n)(K:Set (Points n))(compact:IsCompact K)(apart:K⊆conf n),
      WilsonOriginalBlissRegisteredResponse.Measured R F bliss J level shift
        fund.2.1.paid.stoves simple Q
        (WilsonPositionProgramArithmeticPinnedPrescription.original (AUX:=AUX) R
          (a:=a) (ε:=ε) schedule.1 schedule.2 slow (branches R) p color Z matchMS Q calibration
          floor hd ratio slow.2 nonempty K compact apart) :=
  WilsonOriginalBlissRegisteredResponse.original (AUX:=AUX) (a:=a) (ε:=ε) R F bliss J level shift
    fund.2.1.paid.stoves simple schedule slow (branches R) Z matchMS

end YM.Integration.WilsonOriginalBlissFundedResponse
