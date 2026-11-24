import YM.Integration.WilsonOriginalBlissPositionProgram
import YM.Integration.WilsonOriginalBlissShortHearing

/-! Reflected source hearings for the same MS prescription as the registered position programme. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissReflectedProgram
open scoped Classical BigOperators
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra
open QuadraticLocal.Rebirth ConnectedActivityE6 FullQLocal FullQLocal.RenderedStep
open Multi Exterior WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open Source Labels LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonMixedPassportVote
open Pert.Asymptotics Extra.Histories WilsonOriginalReceivedChain
open scoped Classical BigOperators
open VowsR QuadraticLocal.Affinity Sycamore
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak Tree TraceExtension

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

variable
  (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (seat:root.Tab R.rolls){ψ:ℕ→ℕ}(scroll:VowsR.LawScroll G ψ)
  (books:Mentor.Offices.Books root R.rolls seat ψ)(forecast:Mentor.Forecast root R.rolls seat ψ books)
  {ZΘ:ℝ}{profile:PhysicalNext.ThroughLaunch.Orders}
  (house:Treehouse.VariableHouse R root seat scroll books ZΘ forecast profile)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
  (active:∀j,MintClock.Employment root ψ j (R.rolls.L j))

def Withdrawn (Q:Prescription (Press.portDeck G)) (l:Ultrafilter (ℕ×ℕ)):Prop:=
  ∀{V:Type} [DecidableEq V] [Fintype V] [Nonempty V] (source:Request V)
    (fields:V→MS.Rake.Label (Press.portDeck G)) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ)
    (K grade q tailOrder:ℕ) (tolerance:ℝ), ActualOriginalQLayout.rankCap R fields ≤ grade →
    (∀v,0<w v) → 0<tolerance →
    WilsonOriginalBlissShortHearing.Heard R simple source Q fields μ extra w root seat books forecast l
      K grade q tailOrder tolerance

include bliss house income active in
/-- All finite source rosters use the cutoff filter of this extraction and its fixed prescription. -/
theorem measured (Q:Prescription (Press.portDeck G)):
    Withdrawn R (simple:=simple) root seat books forecast Q l:=by
  intro V _ _ _ source fields μ extra w K grade q tailOrder tolerance ranked positive small
  exact WilsonOriginalBlissShortHearing.original R simple source Q fields μ extra w root seat
    scroll books forecast house income active bliss.lies K grade q (q+1) tailOrder ranked positive small

include house income active in
theorem filed {AUX:Type}(axis:Axis)(lead:PhysMS.Leading F J)(dial:Bool)
    (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))):
    ∃P:Prescription (Press.portDeck G), ∃pair:Main.Match Z simple M P dial,
      WilsonSubcriticalOriginalProgram.Compared F J Z M ∧ ∃Q:Prescription (Press.portDeck G),
      ∃calibration:TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR R) (Press.portDeck G)) Q,
        WilsonOriginalBlissPositionProgram.Book R F bliss J level shift fund schedule slow AUX axis Z M Q calibration pair ∧
        Withdrawn R (simple:=simple) root seat books forecast Q l:=by
  obtain ⟨P,pair,subcritical,Q,calibration,program⟩:=WilsonOriginalBlissPositionProgram.filed
    (AUX:=AUX) R F bliss J level shift fund schedule slow axis lead dial Z M
  exact ⟨P,pair,subcritical,Q,calibration,program,measured R F bliss root seat scroll books forecast house income active Q⟩
include house income active in
theorem original {AUX:Type}(axis:Axis)(lead:PhysMS.Leading F J)(dial:Bool)(L:XSpace.Run):
    ∃(Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (P:Prescription (Press.portDeck G)), Z.run=L ∧ ∃pair:Main.Match Z simple M P dial,
      WilsonSubcriticalOriginalProgram.Compared F J Z M ∧ ∃Q:Prescription (Press.portDeck G),
      ∃calibration:TaylorOKPl M (YM.FVAAlt2.Lobby.Table (Lodge.basisR R) (Press.portDeck G)) Q,
        WilsonOriginalBlissPositionProgram.Book R F bliss J level shift fund schedule slow AUX axis Z M Q calibration pair ∧
        Withdrawn R (simple:=simple) root seat books forecast Q l:=by
  obtain ⟨Z,M,P,geometric,pair,subcritical,Q,calibration,program⟩:=WilsonOriginalBlissPositionProgram.original
    (AUX:=AUX) R F bliss J level shift fund schedule slow axis lead dial L
  exact ⟨Z,M,P,geometric,pair,subcritical,Q,calibration,program,
    measured R F bliss root seat scroll books forecast house income active Q⟩

end YM.Integration.WilsonOriginalBlissReflectedProgram
