import YM.Integration.WilsonOriginalCensusDatedMaterial
import YM.Integration.WilsonReceivedDepositedOrbitalPages

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalLedger
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
open WilsonOriginalCensusDatedMaterial (Material charts)
open WilsonReceivedDepositedOrbitalPages (offered)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonReceivedCompactVerseEntrance
open WilsonReceivedCoverGrade (Same)
variable {G:Gauge}{n q j:ℕ}{k D:Fin n→ℕ}{S:Finset (Fin n)}{A δ σ:ℝ}
  (R:Run G)(Y:Realm G (q+1) Credit.leanC)(lo:Y.anchor≤j+1)(enrolled:Paid R Y lo D k δ σ)
  (N:ℕ)(X:Input Y lo S k D A)(positive:0≤A)(limit:j+1<N)(width:0<σ)
  {I:Type}{n':Side}{P:Passport n' (Fin n)}(B:I→Binder P (Stock.census (Fin n)))
  (c:I→Fin n)(inside:∀l,(B l).mode.val⊆S)(pin:∀l,c l∈(B l).mode.val)
  (deep:∀l,0 < mass k (B l).mode.val)(y:Fin n → Cover)(t:Case D)
  (closed:Cloze D k Y Credit.leanC)(tickets:Insure n (mass k univ) Y Credit.leanC)

def book:Material R N (j+1) q k σ B where
  tests:=D
  available:=S
  amplitude:=A
  allowance:=δ
  realm:=Y
  start:=lo
  paid:=enrolled
  prior:=X
  nonneg:=positive
  lower:=limit
  radius:=width
  pin:=c
  included:=inside
  marked:=pin
  positive:=deep
  root:=fun l=>y (c l)
  source:=fun _=>t
  frill:=fun l=>front (J:=(B l).mode.val) (c l) y
  closed:=closed
  tickets:=tickets

local notation "H" => book R Y lo enrolled N X positive limit width B c inside pin deep y t closed tickets

variable (old:Outerm G D)(well:Wellness k old){s A₀:ℝ}(hs:0<s)(base:1≤A₀)
  (cover:CoverBill old q s A₀)(bound:∀y J,Same q (output X J N y) (old y J))

include well hs base cover bound in
theorem original [Fintype I](per:ℕ)(F:Forest (WilsonVacuumPreResetStationaryChange.step R j per).ratio)
    (h:n'.val∣(WilsonVacuumPreResetStationaryChange.fine R j per).val)(x:Wallet (room (Fin n)))
    (U:fieldDir G (WilsonVacuumPreResetStationaryChange.coarse R j per) 1)(z:Precision.Key F G→ℝ)
    (r:ℕ)(through:r≤q)(slot:Hot (Board (Stock.census (Fin n)) r)):
    WilsonOriginalCensusPaidForest.value B R N j per (by omega) F h x (charts H) U z r slot=
    WilsonOriginalCensusPaidForest.value B R N j per (by omega) F h x
      (fun l=>offered old k q y t (B l).mode.val (c l)) U z r slot:=by
  let a:=(Join.right slot.val).val.card
  have paid:a≤r:=by simpa only [Fintype.card_fin] using (Finset.card_le_univ (Join.right slot.val).val)
  have ray (l:I):WilsonOriginalCensusPaidForest.ray B R N j per (show j<N by omega) F h x
      (charts H) U z l a=WilsonOriginalCensusPaidForest.ray B R N j per (by omega) F h x
        (fun l=>offered old k q y t (B l).mode.val (c l)) U z l a:=by
    unfold WilsonOriginalCensusPaidForest.ray
    have eqn:=WilsonReceivedDepositedOrbitalPages.original R Y lo enrolled N (c l) X (inside l)
      (pin l) positive limit t old well hs base cover bound y per F h (B l).center a (paid.trans through)
    change _*Complex.ofReal (MvPolynomial.eval _ (coeff a _))=_
    rw [show coeff a (WilsonOriginalFoldedMarkedRightColumn.before R N j per (by omega) F
        (WilsonOriginalPrimerReplicatedInk.located h (B l).center ((charts H) l (WilsonVacuumPreResetStationaryChange.fine R j per))))=_
      from eqn]
  unfold WilsonOriginalCensusPaidForest.value
  dsimp only
  simpa only [a] using congrArg (fun f:I→ℂ=>
    (((Join.right slot.val).val.card.factorial:ℕ):ℂ)*
      (if (Join.left slot.val).val.Nonempty then ∑l:I, if (B l).mode=Join.left slot.val then f l else 0
       else _)) (funext ray)

end YM.Integration.WilsonReceivedDepositedOrbitalLedger
end
