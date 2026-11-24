import YM.Integration.WilsonOriginalCensusFaceSites
import YM.Integration.WilsonOriginalCensusDatedCollarPurchase

/-! The finite ordinary panel on its genuine public sites has one registered
front per proper face. Its full period budget is controlled by that face’s
actual wallet and test, independently of all later choices of UV cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFaceCalendar
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

open WilsonOriginalConnectedSubmission (address)
open WilsonOriginalCensusDatedMaterial (Material)
open WilsonCoeffUV.Wheel.Address (toe)
variable {G:Gauge}{n:ℕ}(side:Side)(y:Fin n → Cover)
local notation "J" => Stock.census (Fin n)
local notation "I" => Hot (J)


open WilsonOriginalCensusFaceSites (binder journal pin root frill)
open WilsonOriginalCensusDatedHeldTariff (Rates)
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Winding

theorem housing (R:Run G)(j:ℕ):∀ᶠ per:ℕ in atTop,∀n₀:Side,
    (R.family.side j per).val ∣ n₀.val → ∀s:I,
    4*crestCard (toe s.val.val (pin s) (root y s) (frill y s)) s.val.val < n₀.val:=by
  have grow:Tendsto (fun p:ℕ=>(R.family.side j p).val) atTop atTop:=
    (show StrictMono (fun p:ℕ=>(R.family.side j p).val) from fun _ _ h=>
      Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator j).pos).tendsto_atTop
  have covers (s:I):∀ᶠ per:ℕ in atTop,
      4*crestCard (toe s.val.val (pin s) (root y s) (frill y s)) s.val.val < (R.family.side j per).val:=
    tendsto_atTop.1 grow (4*crestCard (toe s.val.val (pin s) (root y s) (frill y s)) s.val.val+1)
  filter_upwards [eventually_all.2 covers] with per paid
  intro n₀ fit s
  exact (paid s).trans_le (Nat.le_of_dvd n₀.pos fit)

variable (R:Run G)(N i q:ℕ)(k tests:Fin n→ℕ)(σ amplitude allowance:ℝ)
  (realm:Realm G (q+1) Credit.leanC)(start:realm.anchor ≤ i)
  (paid:Paid R realm start tests k allowance σ)
  (prior:Input realm start (univ:Finset (Fin n)) k tests amplitude)
  (funded:0 ≤ amplitude)(live:i < N)(hs:0 < σ)
  (positive:∀v,0 < k v)(test:Case tests)
  (closed:Cloze tests k realm Credit.leanC)(tickets:Insure n (mass k univ) realm Credit.leanC)


local notation "lower" => journal side y R N i q k tests σ amplitude allowance realm start paid prior funded live hs positive test closed tickets

theorem balance (x:Affinity.Wallet (room (Fin n)))(s:I):
    WilsonOriginalCensusDatedHeldTariff.salary lower x s.val=
      ‖∏v∈s.val.val,(x v).val‖*‖touch test s.val.val‖:=by
  change (∑z:I,if s.val=z.val then ‖∏v∈z.val.val,(x v).val‖*
    ‖touch test z.val.val‖ else 0)=_
  rw [sum_eq_single s]
  · simp
  · intro z _ different
    exact if_neg (fun eq=>different (Subtype.ext eq).symm)
  · simp

end YM.Integration.WilsonOriginalCensusFaceCalendar
end
