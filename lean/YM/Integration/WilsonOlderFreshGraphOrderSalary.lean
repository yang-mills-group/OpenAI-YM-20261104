import YM.Integration.WilsonOlderFreshGraphReceivingFigure

/-! The actual word salary pays a geometric factor per derivative of its
support charge, including ranks with a large spatial strip. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphOrderSalary
open Wilson RG QuadraticLocal.Earn Next.Scheduling
open scoped Matrix.Norms.Frobenius

theorem slots (G:Gauge)(P j:ℕ) : ((2:ℝ)^P)^j ≤ Wages.slotCost G P j 0:=by
  have shield:1 ≤ 2*(G.colorScale+1):=by linarith [G.colorScale_pos]
  have gain:1 ≤ 1+G.colorScale⁻¹*‖(1:G.Mat)‖:=by
    linarith [mul_nonneg (inv_nonneg.mpr G.colorScale_pos.le) (norm_nonneg (1:G.Mat))]
  have margin:(2:ℝ)^P ≤ Wages.margin G P 0:=by
    simp only [Wages.margin,Nat.cast_zero,zero_add,one_pow,mul_one]
    exact le_mul_of_one_le_left (by positivity) shield
  calc
    _=1*((2:ℝ)^P)^j:=by simp
    _≤_:=mul_le_mul gain (pow_le_pow_left₀ (by positivity) margin _) (by positivity) (by linarith)

theorem startup (G:Gauge)(s P j:ℕ): (2:ℝ)^(Wages.grade s P j) ≤ Wages.startup G s P j:=by
  have two:(1:ℝ) ≤ 2^j:=one_le_pow₀ (by norm_num)
  calc
    _=((2:ℝ)^j*((2:ℝ)^P)^j)^s:=by
      simp only [Wages.grade,pow_mul,pow_add,pow_one,mul_pow]
      rw [mul_comm]
    _≤((2:ℝ)^j*Wages.slotCost G P j 0)^s:=by gcongr;exact slots ..
    _≤_:=le_mul_of_one_le_left (by positivity [Wages.slot_ge G P j 0]) two

theorem begins (G:Gauge)(B:BudgetPoint){K:ℝ}(one:1≤K)(s:ℕ):
    (2:ℝ)^(B.power*B.order+Invoice.memories B s) ≤ Invoice.liberty G (B.power*B.order) s B.power B.order B.B K:=by
  have floor:(2:ℝ)≤(B.B:ℝ)+2:=by linarith [(Nat.cast_nonneg B.B : (0:ℝ)≤B.B)]
  have sc:0≤Wages.startup G s B.power B.order:=(pow_nonneg (by norm_num : (0:ℝ)≤2) _).trans (startup G s B.power B.order)
  have income:=pow_nonneg (zero_le_one.trans one) s
  calc
    _=(2:ℝ)^(Invoice.memories B s)*1*(2:ℝ)^(B.power*B.order):=by rw [pow_add,mul_one,mul_comm]
    _≤_:=mul_le_mul (mul_le_mul (startup ..) (one_le_pow₀ one) (by positivity) sc)
      (pow_le_pow_left₀ (by norm_num) floor _) (by positivity) (mul_nonneg sc income)

theorem monotone (G:Gauge)(B:BudgetPoint){K:ℝ}(one:1≤K){s t:ℕ}(age:s≤t):
    Invoice.liberty G (B.power*B.order) s B.power B.order B.B K ≤
    Invoice.liberty G (B.power*B.order) t B.power B.order B.B K:=by
  have root:1 ≤ (2:ℝ)^B.order*Wages.slotCost G B.power B.order 0:=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Wages.slot_ge ..)
  have grow:Wages.startup G s B.power B.order ≤ Wages.startup G t B.power B.order:=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ root age) (by positivity)
  have good:0≤Wages.startup G t B.power B.order:=(pow_nonneg (by norm_num : (0:ℝ)≤2) _).trans (startup G t B.power B.order)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul grow (pow_le_pow_right₀ one age) (pow_nonneg (zero_le_one.trans one) _) good) (by positivity)

end YM.Integration.WilsonOlderFreshGraphOrderSalary
end
