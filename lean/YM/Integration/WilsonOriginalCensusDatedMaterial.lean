import YM.Integration.WilsonOriginalCensusPathGaussian
import YM.Integration.WilsonNeutralTwoPrintPathCensusReading

/-! One finite registered roster on one dated physical source. Its two
readings use the same orbit, field orientation, center, and relative frill. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusDatedMaterial
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
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathJet (diagonal)
variable {G:Gauge}{n:ℕ}{R:Run G}{N i q:ℕ}{k:Fin n → ℕ}{σ:ℝ}
  {side:Side}{P:Passport side (Fin n)}{I:Type}{B:I → Binder P (Stock.census (Fin n))}

/-- The finite issued path data, held fixed when the marker wallet or cover side varies. -/
structure Material (R:Run G)(N i q:ℕ)(k:Fin n → ℕ)(σ:ℝ)(B:I → Binder P (Stock.census (Fin n))) where
  tests : Fin n → ℕ
  available : Finset (Fin n)
  amplitude : ℝ
  allowance : ℝ
  realm : Realm G (q+1) Credit.leanC
  start : realm.anchor ≤ i
  paid : Paid R realm start tests k allowance σ
  prior : Input realm start available k tests amplitude
  nonneg : 0 ≤ amplitude
  lower : i < N
  radius : 0 < σ
  pin : I → Fin n
  included : ∀z,(B z).mode.val ⊆ available
  marked : ∀z,pin z ∈ (B z).mode.val
  positive : ∀z,0 < mass k (B z).mode.val
  root : I → Cover
  source : I → Case tests
  frill : ∀z,Frill (B z).mode.val (pin z)
  closed : Cloze tests k realm Credit.leanC
  tickets : Insure n (mass k univ) realm Credit.leanC

variable (H:Material R N i q k σ B)

def words (z:I):Copy G (mass k (B z).mode.val) q σ:=
  slates R H.realm H.start H.paid N H.prior H.nonneg H.lower H.radius.le B H.pin H.included H.marked H.positive H.root H.source H.frill z

def charts (z:I)(a:Side)(y:Site a):PChart G a:=
  WilsonNeutralTwoPrintPathCopies.chart H.realm H.start N (H.pin z) H.prior (H.root z) (H.source z) (H.frill z) a y

theorem admitted (z:I)(a:Side)(y:Site a):
    shellK (mass k (B z).mode.val) (charts H z a y) ∧ ∀d,Pure (charts H z a y d):=
  WilsonNeutralTwoPrintPathCopies.admitted R H.realm H.start H.paid N (H.pin z) H.prior
    (H.included z) (H.marked z) H.nonneg H.lower (H.root z) (H.source z) (H.frill z) a y

theorem matched (z:I):WilsonOriginalPrimerStampedRay.Matched (words H z) (charts H z):=
  WilsonNeutralTwoPrintPathCopies.coordinates R H.realm H.start H.paid N (H.pin z) H.prior
    (H.included z) (H.marked z) H.nonneg H.lower (H.positive z) H.radius.le (H.root z) (H.source z) (H.frill z)
    H.radius H.closed H.tickets

def mounts:=mounted B (fun z=>(words H z).rows (WilsonOlderFreshGraphPointWallet.point (B z).center) disk)

def datum [Fintype I](x:Affinity.Wallet (room (Fin n)))(s:Hot (Stock.census (Fin n)))(d:ℕ)(a:Stationary.Link G side):ℂ:=
  ∑z:I,if s.val=(B z).mode then (∏v∈(B z).mode.val,(x v).val)*Complex.ofReal
    (WilsonNeutralTwoPrintPathJet.diagonal (mass k (B z).mode.val+d)
      (WilsonNeutralTwoPrintPathRead.relative H.realm H.start N (H.pin z) H.prior (H.root z) (H.source z) (H.frill z) d)
      (a ∘ jog (B z).center)) else 0

theorem reading [Fintype I]{p':Passport side (Fin n)}{μ:Type}
    (low:μ → Row p' (Stock.census (Fin n)) G (Affinity.Wallet (room (Fin n))))
    (placed:p'=P)(names:μ=((z:I)×(words H z).Roster))(ink:HEq low (mounts H))
    {w:Fin n → ℝ}{σ₀ expense:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada low w k σ₀ expense order seats shelf)(width:0 < σ₀)
    (x:Affinity.Wallet (room (Fin n)))(layout:Layout G)(tape:Finset Age)
    (s:Hot (Stock.census (Fin n)))(d:ℕ)(through:d ≤ q)(a:Stationary.Link G side):
    (peek dvd_rfl low k layout tape x d a).part s.val=datum H x s d a:=
  WilsonNeutralTwoPrintPathCensus.received R H.realm H.start H.paid N H.prior H.nonneg H.lower H.radius.le B
    H.pin H.included H.marked H.positive H.root H.source H.frill (words H) (fun _=>rfl)
    low placed names ink stock width H.radius H.closed H.tickets x layout tape s d through a

end YM.Integration.WilsonOriginalCensusDatedMaterial
end
