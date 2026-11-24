import YM.Integration.WilsonOriginalFixedTestCensusGeometry

/-! The actual sibling ticket after pricing each dated input at its own dose and direction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFixedTestCensusTickets
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
variable {G:Gauge}{n N i q:ℕ}{k:Fin n → ℕ}{σ:ℝ}{R:Run G}{side:Side}
  (y:Fin n → Cover)(L:Material R N i q k σ (binder side y))(t:Case L.tests)
  (held:Addressed y L t)
local notation "labels" => Hot (Stock.census (Fin n))

local notation "χ" => R.family.path.levels.clock.hatBeta i
local notation "C₀" => ((q+1:ℕ):ℝ)*((mass k univ+q+1:ℕ):ℝ)
local notation "roof" => ((Fintype.card (labels):ℕ):ℝ)*(C₀)
local notation "weight" => WilsonIndependentCollarMaterialWallet.bill L
local notation "tickets" b:max => fun v=>b v*max 1 (WilsonOriginalMixedBlockBudget.roots (binder side y) (weight b))

include held in
theorem row (s:labels)(b:Fin n → ℝ)(basePos:∀v,0<b v)
    (paid:∀v,‖t v‖*L.amplitude ≤ b v):
    weight b s ≤ (C₀)*χ^L.allowance:=by
  have native:=WilsonOriginalFixedTestCensusGeometry.submitted y L t held s
  have price:=WilsonIndependentCollarMaterialCost.original L s
  rw [held.ink s] at price
  have H0:0 ≤ χ:=zero_le_one.trans (R.alloy.B.a.fits.delayed i).le
  have rnn:0 ≤ χ^L.allowance:=Real.rpow_nonneg H0 _
  have marked:(∏v∈s.val.val,‖t v‖)*L.amplitude^s.val.val.card ≤ Poly.toll b s.val:=by
    rw [Poly.toll,←Finset.prod_const (s:=s.val.val) (b:=L.amplitude),←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun v _=>mul_nonneg (norm_nonneg _) L.nonneg) (fun v _=>paid v)
  have horizon:mass k s.val.val ≤ mass k univ:=Finset.sum_le_sum_of_subset (Finset.subset_univ s.val.val)
  have a:((q+1:ℕ):ℝ)*((mass k s.val.val+q+1:ℕ):ℝ) ≤ (C₀):=by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right horizon _) _
  change Real.exp (σ*((binder side y) s).length)*WilsonIndependentCollarSlateIntensity.amount (words L s)
    ((binder side y) s).center/Poly.toll b s.val ≤ _
  apply (div_le_iff₀ (Poly.worth basePos s.val)).mpr
  refine (native.trans price).trans ?_
  change ((q+1:ℕ):ℝ)*((mass k s.val.val+q+1:ℕ):ℝ)*
    ((∏v∈s.val.val,‖t v‖)*|χ^L.allowance*L.amplitude^s.val.val.card|) ≤ _
  rw [abs_of_nonneg (mul_nonneg rnn (pow_nonneg L.nonneg _))]
  calc
    _ = (((q+1:ℕ):ℝ)*((mass k s.val.val+q+1:ℕ):ℝ)*χ^L.allowance)*
        ((∏v∈s.val.val,‖t v‖)*L.amplitude^s.val.val.card):=by ring
    _ ≤ _:=mul_le_mul (mul_le_mul_of_nonneg_right a rnn) marked
      (mul_nonneg (Finset.prod_nonneg fun _ _=>norm_nonneg _) (pow_nonneg L.nonneg _))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) rnn)

include held in
theorem rooted (b:Fin n → ℝ)(basePos:∀v,0<b v)(paid:∀v,‖t v‖*L.amplitude ≤ b v):
    WilsonOriginalMixedBlockBudget.roots (binder side y) (weight b) ≤ (roof)*χ^L.allowance:=by
  have H0:0 ≤ χ:=zero_le_one.trans (R.alloy.B.a.fits.delayed i).le
  have nn:0 ≤ (C₀)*χ^L.allowance:=mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Real.rpow_nonneg H0 _)
  apply Finset.sup'_le
  intro c _
  calc
    _ ≤ ∑_s:labels,(C₀)*χ^L.allowance:=by
      apply Finset.sum_le_sum; intro s _
      split_ifs
      · exact row y L t held s b basePos paid
      · exact nn
    _ = _:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

include held in
/-- A base paying the amplitude and the common test leaves two clock powers for the entire material. -/
theorem original (b:Fin n → ℝ)(basePos:∀v,0<b v)(paid:∀v,‖t v‖*L.amplitude ≤ b v)
    (one:L.allowance ≤ 1)(stage:(roof) ≤ χ)(v:Fin n):
    (tickets b) v ≤ b v*χ^2:=by
  have H1:1 ≤ χ:=(R.alloy.B.a.fits.delayed i).le
  have H0:0 ≤ χ:=zero_le_one.trans H1
  have rootPaid:=rooted y L t held b basePos paid
  have expPaid:χ^L.allowance ≤ χ:=by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le H1 one
  have endPaid:(roof)*χ^L.allowance ≤ χ^2:=by
    rw [pow_two];exact mul_le_mul stage expPaid (Real.rpow_nonneg H0 _) H0
  exact mul_le_mul_of_nonneg_left (max_le (one_le_pow₀ H1) (rootPaid.trans endPaid))
    (basePos v).le

end YM.Integration.WilsonOriginalFixedTestCensusTickets
end
