import YM.Integration.WilsonReceivedCloseQNamedBirth
import YM.Integration.WilsonReceivedCompactMixedSites

/-! Locations retained by the mixed physical passport on its two actual birth meshes. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section

namespace YM.Integration.WilsonReceivedCompactQBirthSites
open Finset Lattice Wilson RG QuadraticLocal.Earn PhysicalNext.Repeat.Legato FullQLocal.RenderedStep
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

variable {G:Gauge} (R:Run G) {V:Type} [Fintype V] [DecidableEq V]
  {B₁ B₂:MS.Local.Physical.Deck G} {b per:ℕ}
local notation "Sites" d:max => V→Site (R.family.side d per)
local notation "sheet" => Pane.panel R.alloy (b+1) (R.alloy.B.a.S.oneStep (b+1) per).exact_size

def Located (old:Finset V) (top:Sites ((b+1)+1)) (fine:Sites (b+1))
    (P:Passport (R.family.side (b+1) per) V):Prop :=
  ∀v,P.origin v=if v∈old then (sheet).ratio.parent (top v) else fine v

omit [Fintype V] in
theorem original (J₁ J₂:Request V) (u₁:V→MS.Rake.Label B₁) (u₂:V→MS.Rake.Label B₂)
    (old:Finset V) (top:Sites ((b+1)+1)) (fine:Sites (b+1)) :
    let U:=paper (ActualOriginalQPointSetup.pointDatum R J₁ per ((b+1)+1) top) u₁
    let F:=paper (ActualOriginalQPointSetup.pointDatum R J₂ per (b+1) fine) u₂
    Located R old top fine
      (WilsonMixedPassportRows.passport (WilsonMixedPassportRows.owner (U.coarser (sheet).ratio) F old)) := by
  dsimp only
  intro v
  have upper : ActualRunQlocalNativeTuple.root (ActualOriginalQPointSetup.pointDatum R J₁ per ((b+1)+1) top) v=top v :=
    ActualOriginalQPointDatum.root_eq R per ((b+1)+1) top (fun a=>(J₁.tests a).D) (fun _=>0) v
  have lower : ActualRunQlocalNativeTuple.root (ActualOriginalQPointSetup.pointDatum R J₂ per (b+1) fine) v=fine v :=
    ActualOriginalQPointDatum.root_eq R per (b+1) fine (fun a=>(J₂.tests a).D) (fun _=>0) v
  by_cases taken:v∈old
  · simp only [WilsonMixedPassportRows.passport,WilsonMixedPassportRows.owner,taken,if_true,
      Passport.coarser,Function.comp_apply,WilsonOriginalProjectedCurvaturePassport.paper,upper]
    rfl
  · simp only [WilsonMixedPassportRows.passport,WilsonMixedPassportRows.owner,taken,if_false,WilsonOriginalProjectedCurvaturePassport.paper,lower]

end YM.Integration.WilsonReceivedCompactQBirthSites
