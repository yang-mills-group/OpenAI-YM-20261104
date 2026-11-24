import YM.Integration.WilsonOlderFreshGraphFactorialTariff

/-! Separate the spatial derivative invoice into its original nonnegative
factors before lowering the reporting horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphInvoiceFace
open RG Wilson QuadraticLocal.Earn Push.AbsoluteSums Next.Scheduling
open scoped BigOperators

def span (B:BudgetPoint)(s:ℕ) := B.power*B.order+Invoice.memories B s
def stipend (G:Gauge)(B:BudgetPoint)(K:ℝ)(s:ℕ):=
    Invoice.liberty G (B.power*B.order) s B.power B.order B.B K
def layers (B:BudgetPoint)(s:ℕ)(θ:ℝ):=θ⁻¹^(4+span B s)*((4+span B s).factorial:ℝ)*Real.exp θ
def common (B:BudgetPoint)(s seats:ℕ)(a θ:ℝ):=
    Real.exp (a*Invoice.tax s seats)*(Footprint.spread 1 (B.B+2):ℝ)*(1-Real.exp (-θ))⁻¹

theorem group (G:Gauge)(B:BudgetPoint)(K:ℝ)(s seats:ℕ)(a θ:ℝ):
    Invoice.price B K s seats a θ G=common B s seats a θ*(stipend G B K s*layers B s θ):=by
  simp only [Invoice.price,Footprint.payment,Footprint.degreeIncome,common,layers,span,stipend]
  ring

theorem balance (B:BudgetPoint)(s seats:ℕ){a θ:ℝ}(ax:0≤a)(hθ:0<θ):1 ≤ common B s seats a θ:=by
  have volume:1≤Footprint.spread 1 (B.B+2):=by
    unfold Footprint.spread Animals.ballCost
    simp only [one_mul]
    exact Nat.one_le_pow _ _ (by omega)
  have tax:0≤Invoice.tax s seats:=by unfold Invoice.tax;positivity
  have small:Real.exp (-θ)<1:=Real.exp_lt_one_iff.mpr (by linarith)
  have rate:1≤(1-Real.exp (-θ))⁻¹ :=
    (one_le_inv₀ (sub_pos.mpr small)).mpr (sub_le_self _ (Real.exp_pos _).le)
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (Real.one_le_exp (mul_nonneg ax tax)) (by exact_mod_cast volume)) rate

theorem common_le (B:BudgetPoint){s t:ℕ}(n:s≤t)(seats:ℕ){a θ:ℝ}(ax:0≤a)(hθ:0<θ):
    common B s seats a θ ≤ common B t seats a θ:=by
  have diff:Invoice.tax s seats≤Invoice.tax t seats:=by unfold Invoice.tax;gcongr
  have small:Real.exp (-θ)<1:=Real.exp_lt_one_iff.mpr (by linarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left diff ax)) (Nat.cast_nonneg _))
    (inv_nonneg.mpr (sub_pos.mpr small).le)

theorem layers_le (B:BudgetPoint){s t:ℕ}(n:s≤t){θ:ℝ}(hθ:0<θ):
    layers B s θ ≤ layers B t θ*Real.exp θ:=by
  have degree:4+span B s≤4+span B t:=by unfold span Invoice.memories Wages.grade;gcongr
  exact mul_le_mul_of_nonneg_right (WilsonOlderFreshGraphFactorialTariff.lower hθ degree) (Real.exp_pos _).le

end YM.Integration.WilsonOlderFreshGraphInvoiceFace
end
