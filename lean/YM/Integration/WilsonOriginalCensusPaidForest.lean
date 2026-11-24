import YM.Integration.WilsonOriginalCensusForestGrades
import YM.Integration.WilsonOriginalThreeGaussianReturn

/-! The finite Gaussian driver on the deposited branch roster. Each original mode uses
its whole copied word at its own deposited site and at its actual source degree. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPaidForest
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
  {q:ℕ}{σ:ℝ}(T:∀l,Copy G (∑v∈(binders l).mode.val,grades v) q σ)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val)(x:Wallet (room V))(L:Layout G)(tape:Finset Age)
  (Z:I→(n:Side)→Site n→PChart G n)(B:fieldDir G (coarse R i per) 1)(z:Precision.Key F G→ℝ)
local notation "own" l:max => (T (l)).rows (WilsonOlderFreshGraphPointWallet.point (binders (l)).center) disk
local notation "M" => mounted binders (fun l=>own l)
local notation "J" => Stock.census V
local notation "joint" => copyColor h M grades (fun a=>(M a).paint x) L tape
local notation "S" => step R i per
local notation "saddle₀" => saddle R N i per F
local notation "K₀" => model R N i per hi

def ray (l:I)(j:ℕ):ℂ:=
  (∏v∈(binders l).mode.val,(x v).val)*Complex.ofReal (MvPolynomial.eval (Sum.elim z (flatten B)) (coeff j
    (WilsonOriginalFoldedMarkedRightColumn.before R N i per hi F (located h (binders l).center (Z l (fine R i per))))))

include tag in
theorem marked {w:V→ℝ}{σ₀ C:ℝ}{d seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C d seats shelf)(σpos:0<σ₀)(hs:0<σ)
    (legal:Legal tape L)(shell:∀l m y,shellK (∑v∈(binders l).mode.val,grades v) (Z l m y))
    (pure:∀l m y j,Pure (Z l m y j))(matched:∀l,WilsonOriginalPrimerStampedRay.Matched (T l) (Z l))
    (s:Hot (J))(j:ℕ)(kept:j≤q):
    readJet ((joint).power s+j) (chartMark (S) F saddle₀ K₀ B z (joint) s)=
    ∑l:I,if (binders l).mode=s.val then ray binders R N i per hi F h x Z B z l j else 0:=by
  rw [WilsonOriginalCensusForestGrades.original binders grades T h x L tape (S) F K₀ saddle₀ B z
    stock σpos hs legal tag (WilsonOriginalJointForestRay.swept R N i per hi F tag) s j]
  apply sum_congr rfl
  intro l _
  by_cases hit:(binders l).mode=s.val
  · rw [if_pos hit,if_pos hit]
    have cap:∀v,‖WilsonOlderFreshGraphArmada.value disk v‖≤1:=fun v=>(v ()).property
    have ear:=WilsonOriginalPrimerStampedRay.received (T l) (Z l) R N i per hi F h
      (WilsonOlderFreshGraphPointWallet.point (binders l).center) disk (project (binders l).mode x)
      (own l) rfl rfl HEq.rfl cap hs L tape (shell l) (pure l) (matched l) q le_rfl B
    have field:=ear name j kept z
    rw [if_pos (show name=submitted (WilsonOlderFreshGraphPointWallet.point (binders l).center) from rfl)] at field
    exact field
  · rw [if_neg hit,if_neg hit]

def value (r:ℕ)(s:Hot (Board (J) r)):ℂ:=
  let j:=(Join.right s.val).val.card
  (j.factorial:ℂ)*(if (Join.left s.val).val.Nonempty then
    ∑l:I,if (binders l).mode=Join.left s.val then ray binders R N i per hi F h x Z B z l j else 0
    else Cloud.paint z (SignedRegisteredMarkedProgram.register F B
      (coeff j (relative R N i per hi F (covered R N i per)))))

theorem original {w:V→ℝ}{σ₀ C:ℝ}{d seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ₀ C d seats shelf)(σpos:0<σ₀)(hs:0<σ)
    (legal:Legal tape L)(shell:∀l m y,shellK (∑v∈(binders l).mode.val,grades v) (Z l m y))
    (pure:∀l m y j,Pure (Z l m y j))(matched:∀l,WilsonOriginalPrimerStampedRay.Matched (T l) (Z l))
    (e:ℕ)(quiet:SeriesA G)(r:ℕ)(kept:r≤q)(s:Hot (Board (J) r)):
    Cloud.paint z (driver R N i per hi F tag (joint) B e quiet r s)=
      value binders R N i per hi F h x Z B z r s:=by
  have well:Bulk.Well (joint):=(copy_standard h M grades (fun a=>(M a).paint x) L tape
    (Air.license M _ grades w stock σpos (fun a=>stock.honor a x)) legal).1
  rw [WilsonOriginalForestDriverReading.original R N i per hi F tag (joint) B z e quiet well r s]
  unfold value
  by_cases live:(Join.left s.val).val.Nonempty
  · simp only [if_pos live,dif_pos live]
    apply congrArg (((Join.right s.val).val.card.factorial:ℂ)*·)
    exact marked binders grades T R N i per hi F tag h x L tape Z B z stock σpos hs legal shell pure matched
      ⟨Join.left s.val,live⟩ _ ((Order.order_limit r (Join.right s.val)).trans kept)
  · simp only [if_neg live,dif_neg live]

end YM.Integration.WilsonOriginalCensusPaidForest
end
