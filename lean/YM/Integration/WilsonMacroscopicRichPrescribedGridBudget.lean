import YM.Integration.WilsonMacroscopicRichGridUnit
import YM.Integration.WilsonRootedOPEPointCommon
import YM.Integration.WilsonRootedOPEPointRestoration
import YM.Integration.WilsonMacroscopicRichGridDefects
/-! The price of evaluating the original independent prescription with unit
amplitude on every normalized marked test at every genuine fine site. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichPrescribedGridBudget
open Function Filter Set MeasureTheory Lattice RG Wilson Source Labels Analysis Next.Foundations Push.Local
open PhysicalNext PhysicalNext.Repeat.Legato RG05Readout Address Native Pulse Flatten RGComparison.Core16
open OPE PhysMS Spec RG17 Extraction MergeProof.Accent Marker Precision Next.UVStress
open LocalComparison LocalComparison.Global IterationFour IterationFour.Vacuum FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric WilsonLimitConstruction QLocalOriginalQHistory
open WilsonSeparatedOriginalSlabWatchScalarMesh
open scoped Classical BigOperators Topology
variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V]{B:MS.Local.Physical.Deck G}
    (R:Run G)(hG:G.Simple)(v:V → MS.Rake.Label B)(J:Request V)(A:NumericSchedule R.family J)
    (d:LocalFormal.Datum R.family (Stock.census V))(Q:MS.Land.Prescription B)(μ:ℝ)(ord:V → ℕ)
local notation "N₀" => d.level+1
local notation "UV" => Config G (R.family.side (N₀) d.period)
local notation "Sites" => V → Site (R.family.side (N₀) d.period)
local notation "J₀" => ActualOriginalQPointSetup.request R v J
open WilsonMacroscopicRichGridUnit
local notation "w₀" => (ActualOriginalQInitialInput.schedule R hG v J A).inputWidth d.level
local notation "universal" => WilsonRootedOPEPointCommon.scalar R Q v μ ord d.cutoff (w₀)
local notation "cost" => fee R hG v J A d Q μ ord
local notation "buyer" => restored R hG v J A d Q μ ord

theorem original (x:Sites) : cost x=universal:=
  WilsonRootedOPEPointCommon.original R hG Q v μ ord J A d x

theorem same (x y:Sites):buyer x=buyer y:=by
  funext i
  apply Subtype.ext
  funext z
  change (cost x:ℂ)=(cost y:ℂ)
  rw [original R hG v J A d Q μ ord x,original R hG v J A d Q μ ord y]

theorem calibrated (x:Sites)(i:V):
    ((J₀).tests i).Bill ((buyer (fun _=>0) i).val) (universal) ∧
    ((VariableScaling.tests (ActualOriginalQInitialInput.scales R hG v J A d Q x μ ord)
       (buyer (fun _=>0))) i).val 0=1:=by
  rw [same R hG v J A d Q μ ord (fun _=>0) x,←original R hG v J A d Q μ ord x]
  exact ⟨WilsonMacroscopicRichGridUnit.tariff R hG v J A d Q μ ord x i,
    WilsonMacroscopicRichGridUnit.calibrated R hG v J A d Q μ ord x i⟩

theorem purchased (ℓ q:ℕ){ε:ℝ}(ep:0<ε):
    let s:=WilsonRootedOPEPointNormalizer.degree R Q v ord
    ∃δ>0,∀(J:Request V)(A:NumericSchedule R.family J)(d:LocalFormal.Datum R.family (Stock.census V)),
      let width:=(ActualOriginalQInitialInput.schedule R hG v J A).inputWidth d.level
      let M:=WilsonRootedOPEPointCommon.scalar R Q v μ ord d.cutoff width
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.cutoff
      M^ℓ*(δ*g^(q+2*(s*ℓ)))≤ε*g^q:=by
  intro s
  obtain ⟨δ,dp,paid⟩:=WilsonRootedOPEPointRestoration.dated R hG Q v μ ord ℓ q ep
  refine ⟨δ,dp,?_⟩
  intro J A d ww M g
  have check:=paid J A d (fun _=>0)
  simpa only [WilsonRootedOPEPointCommon.original R hG Q v μ ord J A d (fun _=>0)] using check

end YM.Integration.WilsonMacroscopicRichPrescribedGridBudget
