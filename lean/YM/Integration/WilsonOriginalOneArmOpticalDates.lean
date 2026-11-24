import YM.Integration.WilsonOriginalOneArmClearCash
import YM.Integration.WilsonOriginalSparseDatedHeat
import YM.Integration.WilsonOriginalPhysicalCorridorLength

/-! A finite roster's thermal and original occupied-gallery costs on one optical
collar. The opening precedes the physical cutoff, period, and held board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOneArmOpticalDates
open Filter Finset Lattice Wilson RG Marker MeasureTheory
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open WilsonOriginalFullRosterCouplingClock
open WilsonRootedKioskOccupiedSlip WilsonCapturedPrimarySoftPartition
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(simple:G.Simple){V:Type}[Fintype V][DecidableEq V]
local notation "marks" => Stock.census V
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "g" N:max per:max i:max => Pert.Asymptotics.regulatorRun R.family N per i
local notation "spanCost" c:max => (c:ℝ)/Real.log 3

structure At (s:(marks).Mode)(n cost power f d debt level:ℕ)(C η:ℝ)
    (budget:2 ≤ C)(np:0 < n)(load:∀t:(marks).Mode,t.val.card ≤ n)(ep:0 < η)(b i N per:ℕ) : Prop where
  begin_at : (eventually_atTop.mp (WilsonOriginalFullRosterCouplingClock.original R simple n cost power f d C
    (zero_le_two.trans budget))).choose ≤ b
  fixed : WilsonSingleHardRadius.first R simple ≤ b
  mature : WilsonCenteredCaptureClock.first R simple ≤ i
  failed_age : WilsonOriginalMountedFailedHalo.first R simple n
    (Nat.cast_nonneg (work n power f d+1+(wallet f).pole+(raw d).pole)) (by norm_num:0 ≤ (1:ℝ)) ≤ b
  failed : (eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple (work n power f d+2)
    (by norm_num:0 < (1:ℝ)))).choose ≤ i
  clock : H (i+1) ≤ (H i)^2
  jets : ((H i)^level)⁻¹  ≤  C*(g N per (i+1))^(work n power f d+2)
  tilt : g N per (i+1) ≤ 1
  positive : 0 < g N per (i+1)
  wide : (eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose ≤ i
  neighbor : (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ i
  optical : WilsonOriginalCensusFiledClearHearing.Opening R simple n 1 debt power np load (spanCost cost) η
    (div_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num:1 < (3:ℝ))).le) ep b i

theorem original (s:(marks).Mode)(n cost power f d debt level:ℕ)(C η:ℝ)
    (budget:2 ≤ C)(np:0 < n)(load:∀t:(marks).Mode,t.val.card ≤ n)(ep:0 < η)(order:work n power f d+3 ≤ level):
    ∀ᶠ b:ℕ in atTop,∀{i K N per:ℕ},b  ≤  i → i  <  K → K  ≤  N →
      R.family.S.a b/R.family.S.a K ≤ (H b)^cost →
      At R simple s n cost power f d debt level C η budget np load ep b i N per:=by
  have c0:0 ≤ spanCost cost:=div_nonneg (Nat.cast_nonneg _) (Real.log_pos (by norm_num:1 < (3:ℝ))).le
  obtain ⟨tail,start,room⟩:=WilsonOriginalCensusFiledClearHearing.opening R simple n 1 debt power np load
    (spanCost cost) η c0 ep
  obtain ⟨heatDate,heat⟩:=eventually_atTop.mp (WilsonOriginalSparseDatedHeat.original R simple
    (work n power f d+2) level level order order 0 (by norm_num))
  obtain ⟨coupling,thermal⟩:=eventually_atTop.mp (WilsonOriginalCensusChronologicalMoney.thermal R simple)
  obtain ⟨neighbors,clocks⟩:=eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)
  obtain ⟨large,early⟩:=eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop tail,eventually_ge_atTop start,eventually_ge_atTop heatDate,
    eventually_ge_atTop coupling,eventually_ge_atTop neighbors,eventually_ge_atTop large,
    eventually_ge_atTop (eventually_atTop.mp (WilsonOriginalFullRosterCouplingClock.original R simple n cost power f d C (zero_le_two.trans budget))).choose,
    eventually_ge_atTop (WilsonSingleHardRadius.first R simple),eventually_ge_atTop (WilsonCenteredCaptureClock.first R simple),
    eventually_ge_atTop (WilsonOriginalMountedFailedHalo.first R simple n (Nat.cast_nonneg (work n power f d+1+(wallet f).pole+(raw d).pole)) (by norm_num:0 ≤ (1:ℝ))),
    eventually_ge_atTop (eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple (work n power f d+2) (by norm_num:0 < (1:ℝ)))).choose,
    eventually_ge_atTop (eventually_atTop.mp ((RG01.Physical.hats simple R.alloy.B.a).eventually_ge_atTop 20)).choose,
    eventually_ge_atTop (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose] with b stop late ready warm near two caps fixed mature failed failedAt wide neighbor
  intro i K N per bi ik kn re
  have dist:(i-b:ℕ) < K-b:=by omega
  have housing:=WilsonOriginalPhysicalCorridorLength.span R simple cost b (K-b) ⟨i-b,dist⟩
    (show R.family.S.a b/R.family.S.a (b+(K-b)) ≤ (H b)^cost from (show b+(K-b)=K by omega).symm ▸ re)
  have earlyField:=thermal b warm (per:=per) (show b ≤ i+1 by omega) (show i+1 ≤ N by omega)
  have hi:0 < H i:=zero_lt_one.trans (R.alloy.B.a.fits.delayed i)
  have hv:=heat i (ready.trans bi) N per (by omega)
  have cg:0 ≤ (g N per (i+1))^(work n power f d+2):=pow_nonneg earlyField.1.le _
  have step:=clocks i (near.trans bi)
  have base:=early i (two.trans bi)
  change H (i+1) ≤ 2*(H i) at step
  change 2 ≤ H i at base
  refine ⟨caps,fixed,mature.trans bi,failed,failedAt.trans bi,?_,?_,?_,earlyField.1,wide.trans bi,
    neighbor.trans bi,room _ _ stop (late.trans bi) ?_⟩
  · calc
      H (i+1) ≤ 2*(H i):=step
      _ ≤ (H i)^2:=by nlinarith only [mul_nonneg hi.le (sub_nonneg.mpr base)]
  · exact hv.1.trans (by nlinarith only [cg,mul_nonneg cg (sub_nonneg.mpr budget)])
  · linarith only [earlyField.2,earlyField.1.le]
  · simpa only [show b+(i-b)=i by omega] using housing

end YM.Integration.WilsonOriginalOneArmOpticalDates
end
