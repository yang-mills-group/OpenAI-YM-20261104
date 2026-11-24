import YM.Integration.WilsonOriginalFixedTestCensusTickets
import YM.Integration.WilsonOriginalFixedTestCensusBookAddress
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFixedTestCensusPairedTickets
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

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead

open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram

open WilsonOriginalCensusFaceSites (binder port pin frill root)
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonOriginalCensusFaceSheet (Addressed)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express
open WilsonOriginalCensusFaceSites (root)

variable {G:Gauge}{n N j q:ℕ}{k:Fin n → ℕ}{σ₀ σ₁:ℝ}{side₀ side₁:Side}
  (R:Run G)(y₀ y₁:Fin n → Cover)
  (L:Material R N (j+1) q k σ₀ (binder side₀ y₀))(H:Material R N (j+2) q k σ₁ (binder side₁ y₁))
  (t₀:Case L.tests)(t₁:Case H.tests)
local notation "headroom" => ((Fintype.card (Hot (Stock.census (Fin n))):ℕ):ℝ)*
  (((q+1:ℕ):ℝ)*((mass k univ+q+1:ℕ):ℝ))
local notation "χ" => R.family.path.levels.clock.hatBeta (j+1)
local notation "χ₁" => R.family.path.levels.clock.hatBeta (j+2)
local notation "ticket" h:max b:max F:max => fun v=>b v*max 1
  (WilsonOriginalMixedBlockBudget.roots F (WilsonIndependentCollarMaterialWallet.bill h b))

theorem clock (simple:G.Simple) :
    ∀ᶠ i:ℕ in atTop, 2 ≤ R.family.path.levels.clock.hatBeta i ∧
      (headroom) ≤ R.family.path.levels.clock.hatBeta i ∧
      (headroom) ≤ R.family.path.levels.clock.hatBeta (i+1) ∧
      R.family.path.levels.clock.hatBeta (i+1) ≤ 2*R.family.path.levels.clock.hatBeta i:=by
  let A:=R.family.path.levels
  have rise:Tendsto A.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have high:=eventually_atTop.mp (rise.eventually_ge_atTop (headroom))
  filter_upwards [rise.eventually_ge_atTop 2,eventually_ge_atTop high.choose,RG01.Physical.nextHat simple A]
    with i warm late step
  exact ⟨warm,high.choose_spec i late,high.choose_spec (i+1) (late.trans (Nat.le_succ _)),by linarith only [step]⟩

theorem original (lo:Addressed y₀ L t₀)(hi:Addressed y₁ H t₁)
    (b₀ b₁:Fin n → ℝ)(p₀:∀v,0<b₀ v)(p₁:∀v,0<b₁ v)
    (slots₀:∀v,‖t₀ v‖*L.amplitude ≤ b₀ v)(slots₁:∀v,‖t₁ v‖*H.amplitude ≤ b₁ v)
    (δ₀:L.allowance ≤ 1)(δ₁:H.allowance ≤ 1)
    (warm:2 ≤ χ)(gate₀:(headroom) ≤ χ)(gate₁:(headroom) ≤ χ₁)(step:χ₁ ≤ 2*χ)
    (dose:Fin n → ℕ)(d₀:∀v,b₀ v ≤ χ^(dose v))(d₁:∀v,b₁ v ≤ χ^(dose v)):
    (∀v,(ticket H b₁ (binder side₁ y₁)) v ≤ χ^(dose v+4)) ∧
      ∀v,(ticket L b₀ (binder side₀ y₀)) v ≤ χ^(dose v+4):=by
  have x1:1 ≤ χ:= (R.alloy.B.a.fits.delayed (j+1)).le
  have x0:0 ≤ χ:=zero_le_one.trans x1
  have y0:0 ≤ χ₁:=zero_le_one.trans (R.alloy.B.a.fits.delayed (j+2)).le
  have bridge:χ₁ ≤ χ^2:=by rw [pow_two];exact step.trans (mul_le_mul_of_nonneg_right warm x0)
  constructor <;> intro v
  · calc
      _ ≤ b₁ v*χ₁^2:=WilsonOriginalFixedTestCensusTickets.original y₁ H t₁ hi b₁ p₁ slots₁ δ₁ gate₁ v
      _ ≤ χ^(dose v)*(χ^2)^2:=mul_le_mul (d₁ v) (pow_le_pow_left₀ y0 bridge 2) (sq_nonneg _) (pow_nonneg x0 _)
      _ = _:=by rw [pow_add,←pow_mul]
  · calc
      _ ≤ b₀ v*χ^2:=WilsonOriginalFixedTestCensusTickets.original y₀ L t₀ lo b₀ p₀ slots₀ δ₀ gate₀ v
      _ ≤ χ^(dose v)*χ^4:=mul_le_mul (d₀ v) (pow_le_pow_right₀ x1 (by decide:2 ≤ 4)) (sq_nonneg _) (pow_nonneg x0 _)
      _ = _:=by rw [pow_add]

end YM.Integration.WilsonOriginalFixedTestCensusPairedTickets
end
