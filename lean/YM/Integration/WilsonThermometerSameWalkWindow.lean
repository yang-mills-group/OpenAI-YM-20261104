import YM.Integration.WilsonThermometerSameWalkTester
import YM.Integration.WilsonOriginalOffsetRoomCost

/-! The current-date window for the complete physical singleton on the actual reporting budget. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkWindow
open Function Filter Lattice Wilson RG Source Labels PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOriginalDepositedRegularHearing WilsonRetainedMarkedInletRegular
open scoped Classical BigOperators Topology

def length (u:ℕ) (β:ℝ):ℕ:=⌈(u:ℝ)*Real.log β⌉₊

theorem bounds (u:ℕ) {β:ℝ} (one:1 ≤ β) :
    Real.exp (3*(length u β:ℝ)) ≤ Real.exp 3*β^(3*u) ∧
    Real.exp (-100*(length u β:ℝ)) ≤ (β^(100*u))⁻¹ := by
  have pos:0<β:=zero_lt_one.trans_le one
  have nn:0 ≤ (u:ℝ)*Real.log β:=mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one)
  have lo:=(Nat.le_ceil ((u:ℝ)*Real.log β))
  have hi:=(Nat.ceil_lt_add_one nn).le
  change (u:ℝ)*Real.log β ≤ (length u β:ℝ) at lo
  change (length u β:ℝ) ≤ (u:ℝ)*Real.log β+1 at hi
  constructor
  · calc _ ≤ Real.exp (3+((3*u:ℕ):ℝ)*Real.log β):=by
            apply Real.exp_le_exp.mpr
            push_cast
            linarith
         _ = _:=by rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log pos]
  · calc _ ≤ Real.exp (-(((100*u:ℕ):ℝ)*Real.log β)):=by
            apply Real.exp_le_exp.mpr
            push_cast
            linarith
         _ = _:=by rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log pos]

variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C₀" => R.family
local notation "β" i => (C₀).path.levels.clock.hatBeta i

include simple in
theorem original (book:WilsonReportLampForecast.Ready (C₀).path.levels) :
    ∀ᶠ i:ℕ in atTop, ∀ per (P:Rep G ((C₀).side i per)), P.p=(C₀).path.levels.budget i →
    ∀ u:ℕ, Real.exp (3*(length u (β i):ℝ))*cost P.p ≤ (β i)^(3*u+2) ∧
      (100≤P.p.supportExponent → Real.exp (-P.p.supportExponent*(length u (β i):ℝ)) ≤ ((β i)^(100*u))⁻¹) := by
  filter_upwards [WilsonOriginalOffsetRoomCost.original R simple book 0,
    (RG01.Physical.hats simple (C₀).path.levels).eventually_ge_atTop (Real.exp 4)] with i earned high per P atDate u
  have paid:=earned i per le_rfl
  have budget:(R.family.path.rep i per i).p=R.alloy.B.a.budget i:=(R.makes.wilson.represents i per i le_rfl).vac
  have same:P.p=(R.family.path.rep i per i).p:=atDate.trans budget.symm
  rw [←same] at paid
  change cost P.p ≤ Real.exp 1*(β i)^(WilsonReportLampForecast.part 0) at paid
  have c:cost P.p ≤ Real.exp 1*(β i):=by
    simpa [WilsonReportLampForecast.part] using paid
  have one:1≤β i:=(R.alloy.B.a.fits.delayed i).le
  have sides:=bounds u one
  constructor
  · calc _ ≤ (Real.exp 3*(β i)^(3*u))*(Real.exp 1*(β i)):=by
            apply mul_le_mul sides.1 c _ _
            · unfold cost;positivity
            · positivity
         _ = Real.exp (3+1)*(β i)^(3*u)*(β i):=by rw [Real.exp_add];ring
         _ ≤ (β i)*(β i)^(3*u)*(β i):=by
           apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans one)
           exact mul_le_mul_of_nonneg_right (show Real.exp (3+1) ≤ β i by norm_num at *; exact high) (pow_nonneg (zero_le_one.trans one) _)
         _ = _:=by rw [pow_succ,pow_succ];ring
  · intro cap
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg cap) (Nat.cast_nonneg _))).trans sides.2

end YM.Integration.WilsonThermometerSameWalkWindow
end
