import YM.Integration.WilsonReceivedDepositedOrbitalConditioned
import YM.Integration.WilsonReceivedCanonicalSocketWick

/-! On a single original forest the joined temporary norm splits into its ordinary
Wick moments indexed by subsets of the actual deposited, located pieces. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalWick
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
open WilsonOriginalThreePurchasedRays (prescribed)
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
variable {G:Gauge} {n:Side} {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
  {P:Passport n V}(binders:I→Binder P (Stock.census V))(grades:V→ℕ)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val)(x:Wallet (room V))
  (Z:I→(n:Side)→Site n→PChart G n)(B:fieldDir G (coarse R i per) 1)(z:Precision.Key F G→ℝ)
local notation "J" => Stock.census V
open Function Finset Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Blue.Cameo Marker QuadraticLocal QuadraticLocal.Earn FVA1Physical.TwoReset PowerSeries
open scoped Classical BigOperators


open WilsonOriginalCensusPaidForest (ray)
open WilsonOriginalFoldedMarkedRightColumn (before)
open WilsonOriginalCensusPageRays (atLift)
open WilsonOriginalGaussianPaidTable (presented)
open MeasureTheory YM.Comparison.RG02.Cumulants

local notation "finePage" => Fin (Pages n (fine R i per))
local notation "whereFrom" => Option (I × finePage)
local notation "full" => WilsonOriginalCensusPaidForest.value binders R N i per hi F h x Z B z


open WilsonReceivedDepositedOrbitalSlice WilsonReceivedDepositedOrbitalMonomials


open WilsonReceivedDepositedOrbitalPhases WilsonReceivedDepositedOrbitalPaint
open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
open WilsonOriginalMixedGaussianTable (stock)
open private ink from YM.Integration.WilsonOriginalCensusPolyPages
open private flat_constant from YM.Integration.WilsonReceivedCanonicalSocketWick
local notation "Z₁" => I×finePage
local notation "S₁" => Stock.census (Z₁)
local notation "Q₁" => (model R N i per hi).covariance F tag
local notation "vac" => relative R N i per hi F (covered R N i per)
local notation "ins" u:max => before R N i per hi F (Z (u).1 (fine R i per) (page h (binders (u).1).center (u).2).val)
local notation "bill" u:max => ∏v∈(binders (u).1).mode.val,(x v).val
local notation "marker" => fun l:(Z₁)=>(S₁).fire l
local notation "charge" => fun l:(Z₁)=>(bill l)
local notation "rows" => fun l:(Z₁)=>(ins l)

def filed (r:ℕ):Grade (S₁) r:=
  stock (S₁) r (flatten B) (fun S:Finset (Z₁)=>∏u∈S,coefficient (S₁) (marker) (charge) u)
    (fun S=>Wick (Woods G (coarse R i per)) (Q₁) (raiseE (vac)*∏u∈S,(ins u)))

theorem direction (r:ℕ)(s:Hot (Board (S₁) r)):
    Cloud.paint z (primitive binders R N i per hi F h x Z B s)=
      WilsonCapturedPrimaryWindingVerseDeposit.entry (S₁) r (Sum.elim z (flatten B)) (vac) (marker) (charge) (rows)
        (Join.left s.val) (Join.right s.val):=by
  obtain ⟨⟨u,t⟩,placed⟩:=(Join.pairs (S₁) (indices r)).surjective s.val
  change Join.pair u t=s.val at placed
  rw [primitive,←placed,Join.left_pair,Join.right_pair,map_add,map_sum,WilsonCapturedPrimaryWindingVerseDeposit.entry]
  by_cases live:u.val.Nonempty
  · rw [if_neg ((hot_iff_ne _).mp live),map_zero,zero_add,if_pos live,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases occurs:(S₁).fire p=u
    · rw [if_pos occurs.symm,if_pos occurs,WilsonReceivedDepositedOrbitalPaint.marked binders R N i per hi F h x Z B z p t]
      rfl
    · rw [if_neg (Ne.symm occurs),if_neg occurs,map_zero,mul_zero]
  · have dead:u=(S₁).quiet:=not_not.mp (fun h=>live ((hot_iff_ne _).mpr h))
    have thermal:t.val.Nonempty:=by
      apply (hot_iff_ne _).mpr
      intro empty
      exact ((hot_iff_ne _).mp s.property) (by rw [←placed,dead,empty,Join.pair_quiet])
    have blank(p:Z₁):u≠(S₁).fire p:=by
      intro used
      exact live (used ▸ ⟨p,Finset.mem_singleton_self _⟩)
    simp only [if_pos dead,if_neg live,blank,if_false,map_zero,Finset.sum_const_zero,add_zero]
    rw [vacuum,if_pos thermal]
    exact ink R i per F B z _ _

theorem original (r:ℕ):
    WilsonReceivedDepositedOrbitalConditioned.staged binders R N i per hi F tag h x Z B r=
      filed binders R N i per hi F tag h x Z B r:=by
  let input:=fun z (s:Hot (Board (S₁) r))=>(temporary binders R N i per hi F h x Z B z r).part s.val
  let form:=primitive (r:=r) binders R N i per hi F h x Z B
  have head:=WilsonOriginalGaussianPaidTable.original (Board (S₁) r) (Q₁) input
    ((model R N i per hi).symm F tag) ((model R N i per hi).positive F tag).posSemidef form
    (fun z s=>attached binders R N i per hi F h x Z B z s)
  have asTable:WilsonReceivedDepositedOrbitalConditioned.staged binders R N i per hi F tag h x Z B r=
      WilsonOriginalGaussianPaidTable.table (Board (S₁) r) (Q₁) input:=by
    apply Marker.Poly.ext
    intro s
    apply integral_congr_ae
    filter_upwards with z
    change ((temporary binders R N i per hi F h x Z B z r).pass).part s=((lit (Board (S₁) r) (input z)).pass).part s
    exact congrArg (fun T:Grade (S₁) r=>T.pass.part s)
      (lit_identity _ (WilsonReceivedDepositedOrbitalPaint.zero binders R N i per hi F h x Z B z r)).symm
  rw [asTable,←head.1]
  apply WilsonOriginalMixedGaussianTable.integrated (S₁) r (flatten B) (Q₁) ((model R N i per hi).symm F tag)
    (fun S:Finset (Z₁)=>∏u∈S,coefficient (S₁) (marker) (charge) u) (fun S=>raiseE (vac)*∏u∈S,(ins u)) form
  intro z
  exact WilsonCapturedPrimaryWindingVerseDeposit.received (S₁) r (Sum.elim z (flatten B))
    (vac) (marker) (charge) (rows) (fun s=>Cloud.paint z (form s)) (flat_constant R N i per hi F)
    (fun l=>⟨l,Finset.mem_singleton_self l⟩) (direction binders R N i per hi F h x Z B z r)

end YM.Integration.WilsonReceivedDepositedOrbitalWick
end
