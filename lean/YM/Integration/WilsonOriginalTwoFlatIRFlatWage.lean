import YM.Integration.WilsonOriginalTwoFlatIRFlatLedger

/-! Discarding super-target grades of a paid connected copy on the genuine
flat costs the actual funded roll salaries and a positive coupling power. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatWage
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

open WilsonGeneralArityCopyAccount WilsonOriginalCensusDatedMaterial WilsonCoeffUV.Blue
open Primitives.TwoWave AllOrder.Haiku Stationary


open WilsonOriginalTwoFlatIRFlatCopy (grade folded)
open WilsonOriginalTwoFlatIRFlatLedger (folded_unit scalar occupied)
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6
private theorem budget {G:Gauge}{s:Side}{d q:ℕ}{σ:ℝ}(T:Copy G d q σ)(width:0≤σ)
    (o:Site s)(j:Fin (q+1)):
    |grade T o j|≤2^(q+d+2)*T.fare j:=by
  let W:=T.roll j
  let Y (u:W.Ty):=W.leg u
  let mag (u:{z:W.Ty//0<(Y z).atom.magnitude}):ℝ:=‖(Y u.val).atom.unmasked (1:Config G s) o‖
  let typ:={z:W.Ty//0<(Y z).atom.magnitude}
  let cost (u:typ):=2^(q+d+2)*W.price (2*σ) u.val
  have pos:0≤(2:ℝ)^(q+d+2):=by positivity
  have upper (u:typ):mag u≤cost u:=by
    have rank: (Y u.val).r ≤ q+d+2 :=by
      have:=((T.paid j).pinned u.val).tall
      change (Y u.val).r+(Y u.val).roots.length ≤ j.val+d+2 at this
      omega
    have m0:0≤(Y u.val).atom.magnitude:=u.property.le
    have wage:(Y u.val).atom.magnitude≤W.price (2*σ) u.val:=by
      apply le_mul_of_one_le_right m0
      exact Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) width) (Nat.cast_nonneg _))
    change |(Y u.val).atom.unmasked (1:Config G s) o| ≤ _
    calc
      _≤(Y u.val).atom.magnitude*2^(Y u.val).r:=(Y u.val).atom.unmasked_bound _ _
      _≤W.price (2*σ) u.val*2^(q+d+2):=mul_le_mul wage (pow_le_pow_right₀ (by norm_num) rank) (by positivity) (m0.trans wage)
      _=_:=mul_comm _ _
  have cash:RG.SumBudget (fun u:typ=>W.price (2*σ) u.val) (T.fare j):=
    budget_pull (fun u:typ=>u.val) Subtype.val_injective (T.paid j).price
  have reserved:=budget_scale pos cash
  have finite : Summable mag:=Summable.of_nonneg_of_le (fun _=>norm_nonneg _) upper reserved.2.1
  exact (norm_tsum_le_tsum_norm finite).trans ((finite.tsum_le_tsum upper reserved.2.1).trans reserved.2.2)

variable {G:Gauge}{n:ℕ}{R:Run G}{N i q:ℕ}{k:Fin n → ℕ}{σ:ℝ}
  {side:Side}{P:Passport side (Fin n)}{I:Type}{B:I → Binder P (Stock.census (Fin n))}
  (H:Material R N i q k σ B)(z:I)

theorem expense (e:Fin (q+1)):
    |occupied H z e|≤2^(q+mass k (B z).mode.val+2)*(words H z).fare e:=by
  have reg:=WilsonNeutralTwoPrintPathRead.register R H.realm H.start H.paid N (H.pin z)
    H.prior (H.included z) (H.marked z) H.nonneg H.lower (H.positive z) H.radius.le (H.root z)
    (H.source z) (H.frill z) H.radius H.closed H.tickets e (by omega) (0:Stationary.Link G side)
  have eq:(∑a:Fin (q+1),(((words H z).roll a).folded a.val e.val).table side
    (mingle (0:Stationary.Link G side) (WilsonElectedPrimaryTensor.pin (0:Site side))))=occupied H z e:=by
    refine reg.trans ?_
    rw [scalar]
    unfold WilsonNeutralTwoPrintPathRead.relative occupied
    rw [folded_unit]
  simp_rw [folded (words H z) H.radius (0:Site side)] at eq
  rw [Finset.sum_ite_eq',if_pos (mem_univ _)] at eq
  rw [←eq]
  exact budget _ H.radius.le _ _

theorem original (g:ℝ)(hg:0≤g)(small:g≤1)(p:ℕ):
    ‖(∑'a:(words H z).Roster,term (words H z) (B z).center g (1:Config G side) a)-
      Complex.ofReal (∑e:Fin (q+1),if e.val≤p then g^e.val*occupied H z e else 0)‖≤
      g^(p+1)*(2^(q+mass k (B z).mode.val+2)*∑e:Fin (q+1),(words H z).fare e):=by
  rw [WilsonOriginalTwoFlatIRFlatLedger.original,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    ←Finset.sum_sub_distrib,Finset.mul_sum,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e _
  have fit:=expense H z e
  by_cases kept:e.val≤p
  · rw [if_pos kept,sub_self,abs_zero]
    exact mul_nonneg (pow_nonneg hg _) ((abs_nonneg _).trans fit)
  · rw [if_neg kept,sub_zero,abs_mul,abs_of_nonneg (pow_nonneg hg _)]
    exact mul_le_mul (pow_le_pow_of_le_one hg small (by omega)) fit (abs_nonneg _) (pow_nonneg hg _)

end YM.Integration.WilsonOriginalTwoFlatIRFlatWage
end
