import YM.Integration.WilsonOriginalObservedRoseBornChiralClockBill
import YM.Integration.WilsonIndependentConditionedActualCredit

/-! Uniform subpower cost on the original measured collar before either finite regulator. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralClockWindow
open Filter Real Function Lattice Wilson RG RG.Supply Precision PhysicalNext.Repeat.Legato
open Next.Rank
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol Extra.Histories
open WilsonOriginalObservedRoseBornChiralClockBill (Dates Funded Priced)
open WilsonIndependentMatchedFreshInverseIncome (age)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonIndependentConditionedActualCredit (badge)
open scoped Topology Classical
variable {G:Gauge}(R:Run G)
local notation "L" => R.family.path.levels

def envelope (A:ℝ):Credit:=⟨1,max 1 (2+4*A),le_max_left _ _⟩

def schedule (A:ℝ)(m K:ℕ):Dates:=
  ⟨(envelope A).buy (badge R m),zz L m,age L (zz L) m K,(paceT R.family.path.levels.S m K)^(1/4:ℝ)⟩

theorem purchased {A:ℝ}(pos:0≤A)(simple:G.Simple):
    ∀ᶠ m:ℕ in atTop,∀K,m≤K→R.family.path.levels.S.scale K-R.family.path.levels.S.scale m≤A*(1+badge R m)→Funded (schedule R A m K):=by
  have leads:=Station.hat_rate L simple
  filter_upwards [(Real.tendsto_log_atTop.comp leads).eventually_ge_atTop 1] with m large
  change 1≤badge R m at large
  intro K past span
  let h:=badge R m
  let w:=(envelope A).buy h
  have hpos:0<h:=zero_lt_one.trans_le large
  have root:1≤zz L m:=by
    change 1≤1+Real.log h
    linarith [Real.log_nonneg large]
  have clock:zz L m ≤ 2*h:=by
    change 1+Real.log h≤2*h
    linarith [Real.log_le_sub_one_of_pos hpos]
  have day:=WilsonSeparatedPrefixMovingCalendar.days R.family.path.levels.S m K past
  have dy:0≤R.family.path.levels.S.scale K-R.family.path.levels.S.scale m:=le_trans (Nat.cast_nonneg _) day
  have age₀:zz L m ≤ age L (zz L) m K:=by
    change zz L m ≤ zz L m+(R.family.path.levels.S.scale K-R.family.path.levels.S.scale m)+((K-m:ℕ):ℝ)
    linarith [Nat.cast_nonneg (α:=ℝ) (K-m)]
  have bound:age L (zz L) m K≤w:=by
    have smaller:A*(1+h)≤2*A*h:=by nlinarith [mul_nonneg pos (sub_nonneg.mpr large)]
    have scalar:(2+4*A)*h≤w:=by
      change (2+4*A)*h ≤ max 1 (2+4*A)*h^1
      simpa only [pow_one] using mul_le_mul_of_nonneg_right (le_max_right 1 (2+4*A)) hpos.le
    apply le_trans _ scalar
    change zz L m+(R.family.path.levels.S.scale K-R.family.path.levels.S.scale m)+((K-m:ℕ):ℝ)≤_
    change R.family.path.levels.S.scale K-R.family.path.levels.S.scale m≤A*(1+h) at span
    linarith [span.trans smaller]
  have fraction:paceT R.family.path.levels.S m K≤1:=by rw [pace_rep,Real.exp_le_one_iff];linarith
  exact ⟨root.trans (age₀.trans bound),root,age₀.trans bound,root.trans age₀,bound,
    Real.rpow_nonneg (pace_pos R.family.path.levels.S m K).le _,Real.rpow_le_one (pace_pos R.family.path.levels.S m K).le fraction (by norm_num)⟩

theorem original {A:ℝ}(pos:0≤A)(simple:G.Simple){F:Dates→ℝ}(issued:Priced F){η:ℝ}(eta:0<η):
    ∀ᶠ m:ℕ in atTop,∀K,m≤K→R.family.path.levels.S.scale K-R.family.path.levels.S.scale m≤A*(1+badge R m)→
      ‖F (schedule R A m K)‖≤(thermal R m)^(-η):=by
  obtain ⟨T,bill⟩:=issued
  have release:=WilsonIndependentConditionedActualCredit.subpower R simple (T.usingC (envelope A)) eta
  filter_upwards [purchased R pos simple,release] with m paid earned
  intro K past reach
  apply (bill (schedule R A m K) (paid K past reach)).trans
  simpa only [schedule,Credit.stock_up] using earned

end YM.Integration.WilsonOriginalObservedRoseBornChiralClockWindow
