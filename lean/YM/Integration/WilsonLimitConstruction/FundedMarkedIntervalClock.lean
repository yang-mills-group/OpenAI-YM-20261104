import YM.Integration.ActualRunAdjacentHatBeta
import YM.Integration.FullQLocalNumericLogarithmicCost
import YM.WilsonCoeffUV.Vacuum.UV.Budget
import YM.WilsonCoeffUV.Product.I.Decay

/-! All finite interval logarithmic charges are paid on the true original
clock before the choice of periods, later cutoffs or marked positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedMarkedIntervalClock
open Filter Lattice RG RG.Supply Precision PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open scoped Topology

variable {G : Gauge} (R : Run G)
local notation "L₀" => R.family.path.levels

def quote (h m : ℕ) := ((h:ℝ)+3)*Real.log ((L₀).clock.hatBeta m)

theorem log_step (hG : G.Simple) : ∀ᶠ m in atTop,
    Real.log ((L₀).clock.hatBeta (m+1))≤Real.log ((L₀).clock.hatBeta m)+1 := by
  filter_upwards [ActualRunAdjacentHatBeta.three_halves R hG] with m bound
  have pos (i : ℕ) : 0<(L₀).clock.hatBeta i := zero_lt_one.trans ((L₀).fits.delayed i)
  have cmp := Real.log_le_log (pos (m+1)) bound
  change Real.log ((L₀).clock.hatBeta (m+1))≤Real.log ((3/2:ℝ)*(L₀).clock.hatBeta m) at cmp
  rw [Real.log_mul (by norm_num) (pos m).ne'] at cmp
  linarith [Real.log_le_sub_one_of_pos (show 0<(3/2:ℝ) by norm_num)]

theorem calendar (hG : G.Simple) (h : ℕ) :
    ∀ᶠ m in atTop, 1≤quote R h m ∧
      ∀ {e : ℕ} {E : Credit} (Q : Realm G e E), Q.y=zz (L₀) →
        PadRank Q (m+1) (m+1+h) (quote R h m) := by
  let l := fun j=>Real.log ((L₀).clock.hatBeta j)
  have big : Tendsto l atTop atTop := Real.tendsto_log_atTop.comp (WardBin.bell (L₀) hG)
  obtain ⟨start,steps⟩ := eventually_atTop.mp (log_step R hG)
  filter_upwards [eventually_ge_atTop start,big.eventually_ge_atTop 1] with m hm large
  have grown : quote R h m≥(h:ℝ)+3 := by
    simpa only [quote,mul_one,l] using mul_le_mul_of_nonneg_left large (show 0≤(h:ℝ)+3 by positivity)
  have walk (i : ℕ) : l (m+i)≤l m+(i:ℝ) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have more : l ((m+i)+1)≤l (m+i)+1 := steps _ (by omega)
      rw [Nat.add_succ,Nat.cast_succ];linarith
  refine ⟨by linarith [Nat.cast_nonneg (α:=ℝ) h],?_⟩
  intro e E Q hy
  refine ⟨?_,?_⟩
  · intro i lo hi
    let d := i-m
    have point : m+d=i := by dsimp [d];omega
    have dist : (d:ℝ)≤(h:ℝ)+1 := by exact_mod_cast (show d≤h+1 by dsimp [d];omega)
    have move := walk d
    rw [point] at move
    have small := Real.log_le_sub_one_of_pos (Real.log_pos ((L₀).fits.delayed i))
    have slack : (h:ℝ)+1≤((h:ℝ)+1)*l m := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left large (show 0≤(h:ℝ)+1 by positivity)
    rw [hy]
    change 1+Real.log (l i) ≤ ((h:ℝ)+3)*l m
    change Real.log (l i)≤l i-1 at small
    nlinarith only [slack,small,move,dist,large]
  · rw [show m+1+h-(m+1)=h by omega]
    linarith

theorem earned (hG : G.Simple) (T : Credit) (h : ℕ) {V : Type} {J : Request V}
    (A : NumericSchedule R.family J) :
    ∀ᶠ m in atTop, ∀ b : ℕ, m+1 ≤ b → b ≤ m+1+h →
      T.buy (quote R h m)^(b-(m+1))≤A.admittedCost m := by
  let c := (T.x*((h:ℝ)+3)^T.d)^h
  have hc : 0≤c := pow_nonneg (mul_nonneg (zero_le_one.trans T.good) (pow_nonneg (by positivity) _)) _
  filter_upwards [A.logarithmic_cost hG c (T.d*h),calendar R hG h] with m bill dates b lo hi
  have next : 0≤c*Real.log ((L₀).clock.hatBeta (m+1))^(T.d*h) :=
    mul_nonneg hc (pow_nonneg (Real.log_pos ((L₀).fits.delayed _)).le _)
  have all : T.buy (quote R h m)^h≤A.admittedCost m := by
    calc
      T.buy (quote R h m)^h = c*Real.log ((L₀).clock.hatBeta m)^(T.d*h) := by
        simp only [Credit.buy,quote,c,mul_pow,pow_mul];ring
      _ ≤ _ := (le_add_of_nonneg_right next).trans bill
  exact (pow_le_pow_right₀ (T.purchase dates.1) (by omega)).trans all

end YM.Integration.WilsonLimitConstruction.FundedMarkedIntervalClock
end
