import YM.Integration.WilsonOriginalCensusGaussianTable
import YM.Integration.WilsonOriginalCensusCompatibleCopies
import YM.Integration.WilsonReceivedDepositedOrbitalConditioned

/-! The original funded incoming Gaussian with its deposited quiet, on each
occupied and proper face and on the unit, subject to the actual color license. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusStagedCopies
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
variable {G:Gauge} {n:Side} {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
  {P:Passport n V}(binders:I→Binder P (Stock.census V))(grades:V→ℕ)
  {q:ℕ}{σ:ℝ}(T:∀l,Copy G (∑v∈(binders l).mode.val,grades v) q σ)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val)(x:Wallet (room V))(L:Layout G)(tape:Finset Age)
  (Z:I→(n:Side)→Site n→PChart G n)
local notation "own" l:max => (T (l)).rows (WilsonOlderFreshGraphPointWallet.point (binders (l)).center) disk
local notation "M" => mounted binders (fun l=>own l)
local notation "J" => Stock.census V
local notation "joint" => copyColor h M grades (fun a=>(M a).paint x) L tape
local notation "S" => step R i per
local notation "saddle₀" => saddle R N i per F
local notation "K₀" => model R N i per hi


open WilsonOriginalCensusCompatibleCopies (entry plate)
open WilsonOriginalCensusCopyGraphs (graph)
open WilsonReceivedDepositedOrbitalConditioned (staged)
local notation "S₁" => Stock.census (I×Fin (Pages n (fine R i per)))

def pupil (l:I):Hot (J):=⟨(binders l).mode,⟨(binders l).front,(binders l).east⟩⟩

def earned (s:(J).Mode)(K:Poly (S₁)):ℂ:=
  ∑q:Finset I,∑p:q→Fin (Pages n (fine R i per)),entry (J) (pupil binders) s q
    (K.part (plate (graph q p)))

theorem original {w:V→ℝ}{σ₀ C:ℝ}{d seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C d seats shelf)(σpos:0<σ₀)(hs:0<σ)
    (legal:Legal tape L)(shell:∀l m y,shellK (∑v∈(binders l).mode.val,grades v) (Z l m y))
    (pure:∀l m y j,Pure (Z l m y j))(matched:∀l,WilsonOriginalPrimerStampedRay.Matched (T l) (Z l))
    {m e:ℕ}{quiet:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e quiet π Γ)(lo:m ≤ i){τ cash:ℝ}
    (funded:Issued R N (i+1) e (quiet (i+1)) τ cash)
    (b:Stationary.Link G (coarse R i per))(r:ℕ)(retained:r ≤ q)(grade:r ≤ e+2)(s:(J).Mode)(coupling:ℕ):
    let B₀:=Stationary.arm G _ 1 b
    let stockIn:=Bulk.Fk (K₀) F tag (QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2)) (joint)) B₀ r
    let stages:=staged binders R N i per hi F tag h x Z B₀ r
    (Order.observe (J) r (Order.ratio stockIn) coupling).part s=
      earned binders R i per s (Order.observe (S₁) r (Order.ratio stages) coupling) ∧
    (Order.observe (J) r (Order.logMarked stockIn) coupling).part s=
      earned binders R i per s (Order.observe (S₁) r (Order.logMarked stages) coupling):=by
  intro B₀ stockIn stages
  have full:=WilsonOriginalCensusGaussianTable.original binders grades T R N i per hi F tag h x L tape Z
    stock σpos hs legal shell pure matched course lo funded b r retained grade
  have folded:=WilsonReceivedDepositedOrbitalConditioned.original binders grades R N i per hi F tag h x
    Z B₀ (fun l y=>shell l _ y) (fun l y=>pure l _ y) r coupling
  have classed(K:Poly (S₁)):
      (WilsonReceivedDepositedAlias.fold (J) (WilsonReceivedDepositedOrbitalPhases.name binders R i per) K).part s=
      earned binders R i per s K:=WilsonOriginalCensusCompatibleCopies.original (J) (pupil binders) K s
  exact ⟨(congrArg (fun v=>(Order.observe (J) r v coupling).part s) full.1).trans
    ((congrArg (fun v:Poly (J)=>v.part s) folded.1).trans (classed _)),
    (congrArg (fun v=>(Order.observe (J) r v coupling).part s) full.2.1).trans
      ((congrArg (fun v:Poly (J)=>v.part s) folded.2).trans (classed _))⟩

end YM.Integration.WilsonOriginalCensusStagedCopies
end
