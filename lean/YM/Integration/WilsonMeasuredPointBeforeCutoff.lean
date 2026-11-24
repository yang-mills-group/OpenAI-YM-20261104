import YM.Integration.WilsonMeasuredPointNominatedReturn
import YM.Integration.WilsonMeasuredPointUpperToll

/-! Finite original stage purchases and the upper small-coupling gates can be
fixed simultaneously before the period, upper cutoff, itinerary and wallet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointBeforeCutoff
open OPE.Therm
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open WilsonOriginalReceivedChain WilsonMeasuredRankedResidual Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle QuadraticLocal.Earn Primitives.TwoWave
open WilsonNeutralRenderedColumn WilsonOriginalPrimerFiledPages
open WilsonMeasuredTransitionCatalogue
open WilsonMeasuredOriginalCatalogueUnion WilsonEmittedFiledGerm
open QuadraticLocal.Earn
open WilsonMeasuredJointCensusCash
open WilsonEmittedDictionary Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonLimitConstruction.FundedDictionaryPatchPrices
open WilsonEmittedOriginalReturn Push.AbsoluteSums Extra.Histories Extra.Histories.Relay
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker
open MeasureTheory
variable {G:Gauge} (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
variable {k:ℕ} (school:Syl.School k) (q Qwork high:ℕ) {ε:ℝ} (ep:0<ε)
local notation "q₁" => (q+2+2)
local notation "target" d:max q:max => 2*4+(d+1)+1+(q+3)
private theorem micro {ε:ℝ} (ep:0<ε):0<(ε/8)/16:=by positivity
local notation "ep₀" => micro ep
private theorem ready_order {q J:ℕ} (h:2*(q+4+1)+8 ≤ J):2*q+8 ≤ J:=by omega
private theorem ready_age {q k:ℕ} (h:q+4+4 ≤ 3*k+2):q+3 ≤ 3*k+2:=by omega
variable (deep:2*((q+2+2)+4+1)+8 ≤ school.order)(aged:(q+2+2)+4+4 ≤ 3*k+2)
variable (tube:LinkTube G)(programPaid:Covered (program tube) R)
  (strength:∀ i,(R.family.path.levels.budget i).supportExponent ≤ 100)
  (enough:3*(target 4 q) ≤ Qwork)
  (prepared:WilsonReportLampForecast.Ready R.family.path.levels)
  (M₀:WilsonMeasuredRankedMenu.Menu R 4)

def Dated (deep:2*(q₁+4+1)+8 ≤ school.order) (aged:q₁+4+4 ≤ 3*k+2) (j:ℕ) : Prop :=
  (WilsonMeasuredCourseGradeReturn.first R (WilsonMeasuredPointNominatedReturn.reporter Qwork) simple slow tube programPaid strength q enough ep ≤ j) ∧
  (WilsonMeasuredLandedCurrency.first R simple ≤ j) ∧
  (school.horizon ≤ R.alloy.B.a.clock.J j) ∧
  (R.family.ref 4 ≤ j) ∧
  (WilsonOlderFreshGraphReceivingFigure.first R simple ≤ (j+1)) ∧
  (WilsonOlderFreshPointEmittedWallet.activation (inputRank:=(4:ℕ)) R simple slow ≤ (j+1)) ∧
  (school.horizon ≤ R.alloy.B.a.clock.J (j+1)) ∧
  (WilsonOlderFreshGraphPreimageFee.first R simple slow 4 ≤ (j+1)) ∧
  (WilsonMeasuredSemesterSubpower.onset R 1 (half_pos (show (0:ℝ)<1 by norm_num)) ≤ (j+1)) ∧
  (M₀.onset ≤ (j+1)) ∧
  (R.t (4:ℕ) ≤ (j+1)) ∧
  (WilsonCenteredCaptureClock.first R simple ≤ (j+1)) ∧
  (WilsonReceivedSourceGross.opening R simple ≤ (j+1)) ∧
  (WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow.2 prepared ≤ (j+1)) ∧
  (q₁+1+6 ≤ R.alloy.B.a.clock.J (j+1)) ∧
  (WilsonFirstReceivedEarnedFee.opening R simple school.pieces (q₁+4) school.order k deep aged (tolerance_pos R (4:ℕ) q₁ (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀)) ≤ (j+1)) ∧
  (WilsonCoherentMayerMutationIntake.firstDate R simple school.order (show (0:ℝ)<1 by norm_num) le_rfl (tolerance_pos R (4:ℕ) q₁ (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀)) ≤ (j+1)) ∧
  (WilsonOlderSignedOneMarkBooked.opening R simple (school.order+school.horizon+2) q₁ 102 (show 0 < WilsonMeasuredRankedMenu.fee R (4:ℕ) M₀ ((ε/8)/16)/6 from div_pos (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀) (by norm_num)) ≤ (j+1)) ∧
  (WilsonOlderSignedOneMarkCurrency.opening R simple q₁ (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀) ≤ (j+1)) ∧
  (WilsonReceivedMeasuredStampPrice.opening R simple q₁ school.order k (ready_order deep) (ready_age aged) ep₀ ≤ (j+1)) ∧
  (q₁+6*school.pieces ≤ R.alloy.B.a.clock.J (j+1)) ∧
  (WilsonMeasuredSemesterSubpower.onset R 6 zero_lt_one ≤ (j+1)) ∧
  (WilsonMeasuredNeutralFiledStock.onset R simple ≤ (j+1)) ∧
  ((4:ℕ) ≤ R.family.path.levels.clock.J ((j+1)+1)) ∧
  (Sycamore.Boot.need high school ≤ R.alloy.B.a.clock.J ((j+1)+1)) ∧
  (∀ N per:ℕ,(j+1)+1 ≤ N → ((ε/8)/16)*(Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta)^q₁ ≤ 1)


include deep aged in
/-- No numerical threshold here depends on an upper Wilson field. -/
theorem funded :
    ∀ᶠ j:ℕ in atTop,Dated R simple slow school q Qwork high ep tube programPaid strength
      enough prepared M₀ deep aged j:=by
  have clock:Tendsto R.alloy.B.a.clock.J atTop atTop:=R.family.path.levels.fits.deep
  have next:Tendsto (fun j=>R.alloy.B.a.clock.J (j+1)) atTop atTop:=clock.comp (tendsto_add_atTop_nat 1)
  have second:Tendsto (fun j=>R.alloy.B.a.clock.J ((j+1)+1)) atTop atTop:=
    next.comp (tendsto_add_atTop_nat 1)
  filter_upwards [
    eventually_ge_atTop (WilsonMeasuredCourseGradeReturn.first R (WilsonMeasuredPointNominatedReturn.reporter Qwork) simple slow tube programPaid strength q enough ep),
    eventually_ge_atTop (WilsonMeasuredLandedCurrency.first R simple),
    clock.eventually_ge_atTop (school.horizon),
    eventually_ge_atTop (R.family.ref 4),
    eventually_ge_atTop (WilsonOlderFreshGraphReceivingFigure.first R simple),
    eventually_ge_atTop (WilsonOlderFreshPointEmittedWallet.activation (inputRank:=(4:ℕ)) R simple slow),
    next.eventually_ge_atTop (school.horizon),
    eventually_ge_atTop (WilsonOlderFreshGraphPreimageFee.first R simple slow 4),
    eventually_ge_atTop (WilsonMeasuredSemesterSubpower.onset R 1 (half_pos (show (0:ℝ)<1 by norm_num))),
    eventually_ge_atTop (M₀.onset),
    eventually_ge_atTop (R.t (4:ℕ)),
    eventually_ge_atTop (WilsonCenteredCaptureClock.first R simple),
    eventually_ge_atTop (WilsonReceivedSourceGross.opening R simple),
    eventually_ge_atTop (WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow.2 prepared),
    next.eventually_ge_atTop (q₁+1+6),
    eventually_ge_atTop (WilsonFirstReceivedEarnedFee.opening R simple school.pieces (q₁+4) school.order k deep aged (tolerance_pos R (4:ℕ) q₁ (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀))),
    eventually_ge_atTop (WilsonCoherentMayerMutationIntake.firstDate R simple school.order (show (0:ℝ)<1 by norm_num) le_rfl (tolerance_pos R (4:ℕ) q₁ (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀))),
    eventually_ge_atTop (WilsonOlderSignedOneMarkBooked.opening R simple (school.order+school.horizon+2) q₁ 102 (show 0 < WilsonMeasuredRankedMenu.fee R (4:ℕ) M₀ ((ε/8)/16)/6 from div_pos (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀) (by norm_num))),
    eventually_ge_atTop (WilsonOlderSignedOneMarkCurrency.opening R simple q₁ (WilsonMeasuredRankedMenu.fee_positive R (4:ℕ) M₀ ep₀)),
    eventually_ge_atTop (WilsonReceivedMeasuredStampPrice.opening R simple q₁ school.order k (ready_order deep) (ready_age aged) ep₀),
    next.eventually_ge_atTop (q₁+6*school.pieces),
    eventually_ge_atTop (WilsonMeasuredSemesterSubpower.onset R 6 zero_lt_one),
    eventually_ge_atTop (WilsonMeasuredNeutralFiledStock.onset R simple),
    second.eventually_ge_atTop ((4:ℕ)),
    second.eventually_ge_atTop (Sycamore.Boot.need high school),
    (tendsto_add_atTop_nat 1).eventually ((tendsto_add_atTop_nat 1).eventually (WilsonMeasuredPointUpperToll.small R simple ((ε/8)/16)))] with j h_late h_awake h_lowerDate h_ready h_issued h_later h_shelved h_stride h_live h_office h_date h_lateHead h_grossDate h_fareDate h_roomAge h_opened h_recalled h_masks h_soft h_booked h_hardOrder h_fiscal h_threshold h_active h_boot upper
  exact ⟨
    h_late,
    h_awake,
    h_lowerDate,
    h_ready,
    h_issued.trans (Nat.le_succ j),
    h_later.trans (Nat.le_succ j),
    h_shelved,
    h_stride.trans (Nat.le_succ j),
    h_live.trans (Nat.le_succ j),
    h_office.trans (Nat.le_succ j),
    h_date.trans (Nat.le_succ j),
    h_lateHead.trans (Nat.le_succ j),
    h_grossDate.trans (Nat.le_succ j),
    h_fareDate.trans (Nat.le_succ j),
    h_roomAge,
    h_opened.trans (Nat.le_succ j),
    h_recalled.trans (Nat.le_succ j),
    h_masks.trans (Nat.le_succ j),
    h_soft.trans (Nat.le_succ j),
    h_booked.trans (Nat.le_succ j),
    h_hardOrder,
    h_fiscal.trans (Nat.le_succ j),
    h_threshold.trans (Nat.le_succ j),
    h_active,
    h_boot,
    fun N per top=>upper N per top q₁ (Nat.zero_lt_succ (q+2+1))⟩

end YM.Integration.WilsonMeasuredPointBeforeCutoff
end
