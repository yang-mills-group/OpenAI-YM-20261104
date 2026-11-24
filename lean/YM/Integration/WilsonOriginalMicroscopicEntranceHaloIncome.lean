import YM.Integration.WilsonOriginalMicroscopicEntranceOpticalUnits
import YM.Integration.ActualCoarseStagePrice

/-! The original lower flat law pays the whole spatial incidence on the
actual selected upper K stipend. One precision covers every surviving face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHaloIncome
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

def all (t:ℕ):ℕ:=∑a:Fin 3,(t*(d a+1)+rank R (d a))

private theorem used (t:ℕ)(s:(J).Mode):pole R d t s ≤ all R d t:=by
  unfold all WilsonOriginalMicroscopicEntranceOpticalUnits.pole
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem optical (simple:G.Simple){f K t:ℕ}(up:f ≤ K){η:ℝ}(small:η ≤ 1)
    (room:mesh f/mesh K ≤ (H f)^t*(H f)^η):
    mesh f/mesh K ≤ (H K)^(t+1):=by
  have one:1 ≤ H f:=((CF).path.levels.fits.delayed f).le
  have moved:=ActualCoarseStagePrice.hatBeta_mono (CF).path.levels simple up
  have right:(H f)^η ≤ H f:=(Real.rpow_le_rpow_of_exponent_le one small).trans_eq (Real.rpow_one _)
  calc
    _ ≤ (H f)^t*(H f)^η:=room
    _ ≤ (H f)^t*(H f):=mul_le_mul_of_nonneg_left right (pow_nonneg (zero_le_one.trans one) _)
    _ ≤ (H K)^(t+1):=by rw [←pow_succ];exact pow_le_pow_left₀ (zero_le_one.trans one) moved _

variable {N per m k K:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (live:K ≤ N)(top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(start:u  ≤  K)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
   (capture:WilsonCenteredCaptureClock.first R simple  ≤  K)

local notation "K₀" => R.alloy.B.a.budget K
include course top floor start fixed capture live way ticket in
theorem original {f t:ℕ}(up:f ≤ K)(housing:mesh f/mesh K ≤ (H K)^t)
    (o:Fin 3→Site ((CF).side K per))(z:∀a:Fin 3,(CF).label (d a))(V:Fin 3→ℝ)(vp:∀a,0 ≤ V a)
    (earned:∀a,slotFare R d f K z a ≤ (mesh f)^(d a)*V a)(q:ℕ){ε:ℝ}(positive:0<ε)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple (q+all R d t) positive)).choose  ≤  K)
    (s:(J).Mode){i:ℕ}(reach:u ≤ i)(before:i+1 ≤ K):
    ‖units R d K s*actualTransport CF (N:=N) (gap R d N per K o z s.val) ((Nat.le_succ i).trans before) 1‖ ≤ 
    fare R d V s*((count R d s.val:ℝ)*(4*Real.exp ((K₀).supportExponent+2)*(ε/(H K)^q))):=by
  let net:=fun a=>V a/(hike CF K f rate*(1+4*stock CF K))
  let M:=fun a=>(mesh f)^(d a)*net a
  have paid:=WilsonOriginalMicroscopicEntranceUnitRefund.supplied R d z V earned
  have refund:=WilsonOriginalMicroscopicGuardedFlat.power R d π Γ Ψ course live top simple way D Q ticket
    floor start fixed capture o z M paid s.val (q+all R d t) positive late reach before
  let profile:=fare R d V s
  have input:=WilsonOriginalMicroscopicEntranceOpticalUnits.original R d up housing V vp s
  change ‖units R d K s‖*peak R d K M s.val ≤ profile*(H K)^(pole R d t s) at input
  have χ:1 ≤ H K:=((CF).path.levels.fits.delayed K).le
  have hp:0<H K:=zero_lt_one.trans_le χ
  have rate₀:0 ≤ profile:=by
    apply mul_nonneg (by norm_num)
    apply Finset.prod_nonneg
    intro a _
    apply mul_nonneg _ (vp a)
    exact add_nonneg (by norm_num) (zero_le_one.trans (BasisCost.price_pos _))
  have cost:=input.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ χ (used R d t s)) rate₀)
  let tariff:ℝ:=(count R d s.val:ℝ)*(4*Real.exp ((K₀).supportExponent+2))
  have tariff₀:0 ≤ tariff:=by dsimp [tariff];positivity
  have pmax:0 ≤ tariff*(ε/(H K)^(q+all R d t)):=mul_nonneg tariff₀ (div_nonneg positive.le (pow_nonneg hp.le _))
  have initial:=mul_le_mul_of_nonneg_left refund (norm_nonneg (units R d K s))
  rw [norm_mul]
  calc
    _ ≤ (‖units R d K s‖*peak R d K M s.val)*(tariff*(ε/(H K)^(q+all R d t))):=by
      apply initial.trans_eq
      dsimp only [tariff]
      rw [show R.alloy.B.a.clock.hatBeta K=H K from rfl]
      ring
    _ ≤ (profile*(H K)^(all R d t))*(tariff*(ε/(H K)^(q+all R d t))):=mul_le_mul_of_nonneg_right cost pmax
    _=_:=by
      dsimp only [profile,tariff]
      rw [pow_add]
      field_simp [hp.ne']

end YM.Integration.WilsonOriginalMicroscopicEntranceHaloIncome
end
