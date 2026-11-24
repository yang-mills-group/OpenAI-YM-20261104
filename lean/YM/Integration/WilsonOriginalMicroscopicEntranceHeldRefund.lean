import YM.Integration.WilsonOriginalMicroscopicEntranceHeldHalo
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldUnits

/-! The physical K polynomial on the original conditional law, with an explicit boundary-field factor. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldRefund
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open Extra.Histories Extra.Multi Push.AbsoluteSums.Animals
open WilsonOriginalMicroscopicEntranceFiling (units)
open WilsonOriginalMicroscopicEntranceGridBalance (slotFare)
open WilsonOriginalMicroscopicEntranceOpticalUnits (pole rank dye fare)
open WilsonOriginalMicroscopicGuardedFlat (peak count)
open Trace.Physical.Germ Trace.Physical.GermGraph
open scoped BigOperators Classical

variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ)

local notation "CF" => R.family
local notation "J" => Stock.census (Fin 3)
local notation "H" i:max => (CF).path.levels.clock.hatBeta i
local notation "mesh" i:max => (CF).S.a i

open WilsonOriginalMicroscopicEntranceHaloIncome (all)
variable {N per m k K:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (live:K ≤ N)(top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(start:u ≤ K)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
   (capture:WilsonCenteredCaptureClock.first R simple ≤ K)

local notation "K₀" => R.alloy.B.a.budget K
include course top floor fixed capture live way ticket in
theorem original {f t:ℕ}(up:f ≤ K)(housing:mesh f/mesh K ≤ (H K)^t)
    (o:Fin 3→Site ((CF).side K per))(z:∀a:Fin 3,(CF).label (d a))(V:Fin 3→ℝ)(vp:∀a,0 ≤ V a)
    (earned:∀a,slotFare R d f K z a ≤ (mesh f)^(d a)*V a)(q:ℕ){ε:ℝ}(positive:0<ε)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple (q+all R d t) positive)).choose ≤ K)
    (s:(J).Mode){i:ℕ}(reach:u ≤ i)(before:i+1 ≤ K)(W:Config G (R.family.side i per)):
    ‖units R d K s*actualTransport (CF) (N:=N) (gap R d N per K o z s.val) ((Nat.le_succ i).trans before) W‖ ≤ 
      WilsonOriginalMicroscopicEntranceHeldHalo.spring R i N per W*
        (fare R d V s*((count R d s.val:ℝ)*(4*Real.exp ((K₀).supportExponent+2))*(ε/(H K)^q))):=by
  let X:=footprint R d per K o s.val
  let tariff:ℝ:=(count R d s.val:ℝ)*(4*Real.exp ((K₀).supportExponent+2))
  let spring:=WilsonOriginalMicroscopicEntranceHeldHalo.spring R i N per W
  let profile:=fare R d V s
  have hp₁:1 ≤ H K:=((CF).path.levels.fits.delayed K).le
  have hp:0<H K:=zero_lt_one.trans_le hp₁
  have sp:0 ≤ spring:=sq_nonneg _
  have pr:0 ≤ profile:=by
    apply mul_nonneg (by norm_num)
    apply Finset.prod_nonneg
    intro a _
    apply mul_nonneg _ (vp a)
    exact add_nonneg (by norm_num) (zero_le_one.trans (BasisCost.price_pos _))
  have tax:0 ≤ tariff:=by dsimp [tariff];positivity
  have area:(X.card:ℝ) ≤ (count R d s.val:ℝ):=by
    exact_mod_cast (show X.card ≤ count R d s.val from Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a _=>Finset.card_image_le))
  have hot:=WilsonOriginalMicroscopicEntranceHeldHalo.original R π Γ Ψ course live top simple way D Q ticket
    floor reach fixed capture (q+all R d t) positive late before X W
  have sh:=WilsonOriginalMicroscopicEntranceHeldUnits.original R d live up before housing o z V vp earned s W
  let law:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per before W
  let E:=SelectedCofactorAnchoredRegister.hot (G:=G) ((CF).path.rep N per K).p.threshold X
  have budget:law.real E ≤ spring*(tariff*(ε/(H K)^(q+all R d t))):=by
    apply hot.trans
    apply mul_le_mul_of_nonneg_left _ sp
    apply mul_le_mul_of_nonneg_right _ (div_nonneg positive.le (pow_nonneg hp.le _))
    exact mul_le_mul_of_nonneg_right area (by positivity)
  have sub:pole R d t s ≤ all R d t:=Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have total:=mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp₁ sub) pr) budget
    measureReal_nonneg (mul_nonneg pr (pow_nonneg hp.le _))
  apply sh.2.trans (total.trans_eq _)
  dsimp only [profile,spring,tariff]
  rw [pow_add]
  field_simp [hp.ne']

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldRefund
end
