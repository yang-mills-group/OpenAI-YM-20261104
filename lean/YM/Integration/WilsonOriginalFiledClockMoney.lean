import YM.Integration.WilsonOriginalDatedFieldsAtBoard

/-! Fixed reporting exponents of the two actual compact prints issued on one Wilson edge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledClockMoney
open RG Wilson Marker Lattice QuadraticLocal Multi
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open WilsonOriginalMountedRegular WilsonOriginalOccupiedWindow
open scoped BigOperators
variable {G:Gauge}{R:Run G}{V:Type}[DecidableEq V][Fintype V]{marks:Census V}
  {i per:ℕ}{vac:RG.Rep G (R.family.side i per)}{row:Slice R marks vac}
  {lower:Config G (R.family.side i per) → Poly marks}{s:marks.Mode}
  (F:Filing R vac row lower s)

theorem original {H g hi lo C:ℝ}(h k k':ℕ)(H1:1 ≤ H)(gp:0 < g)(gs:g ≤ 1)
    (ch:hi ≤ C)(cl:lo ≤ C)(base:2 ≤ C)
    (ww:F.W ≤ H^h)(ww':F.W' ≤ H^h)(regular:F.regular ≤ H^2)(aged:F.rent ≤ 1)
    (gross:F.gross ≤ (hi/g^k)*H^2)(next:F.nextGross ≤ (lo/g^k')*H)
    (account:F.M=max (F.W*(F.regular+F.rent)) (F.W'*F.nextGross)):
    F.W ≤ C*H^h ∧ F.gross ≤ C*H^2*(g⁻¹)^(max k k') ∧ F.M ≤ C*H^(h+2)*(g⁻¹)^(max k k'):=by
  let z:=g⁻¹
  let d:=max k k'
  have zp:1 ≤ z:=(one_le_inv₀ gp).mpr gs
  have zg:1 ≤ z^d:=one_le_pow₀ zp
  have hh:0 ≤ H:=zero_le_one.trans H1
  have hp:1 ≤ H^2:=one_le_pow₀ H1
  have hc:0 ≤ C:=by linarith only [base]
  have hm:H ≤ H^2:=by nlinarith only [H1,mul_nonneg hh (sub_nonneg.mpr H1)]
  have ud:hi*(g⁻¹)^k ≤ C*z^d:=mul_le_mul ch (pow_le_pow_right₀ zp (le_max_left k k')) (by positivity) hc
  have ld:lo*(g⁻¹)^k' ≤ C*z^d:=mul_le_mul cl (pow_le_pow_right₀ zp (le_max_right k k')) (by positivity) hc
  have og:F.gross ≤ C*z^d*H^2:=by
    rw [div_eq_mul_inv,←inv_pow] at gross
    exact gross.trans (mul_le_mul_of_nonneg_right ud (pow_nonneg hh _))
  have nl:F.nextGross ≤ C*z^d*H^2:=by
    rw [div_eq_mul_inv,←inv_pow] at next
    exact next.trans (mul_le_mul ld hm hh (mul_nonneg hc (zero_le_one.trans zg)))
  have two:2 ≤ C*z^d:=base.trans (le_mul_of_one_le_right hc zg)
  have reg:F.regular+F.rent ≤ C*z^d*H^2:=by
    calc F.regular+F.rent ≤ H^2+1:=add_le_add regular aged
         _ ≤ 2*H^2:=by linarith only [hp]
         _ ≤ _:=mul_le_mul_of_nonneg_right two (pow_nonneg hh _)
  have side:F.M ≤ H^h*(C*z^d*H^2):=by
    rw [account];apply max_le
    · exact mul_le_mul ww reg (add_nonneg F.regular_nn F.rent_nn) (pow_nonneg hh _)
    · exact mul_le_mul ww' nl F.other_nn (pow_nonneg hh _)
  refine ⟨ww.trans (le_mul_of_one_le_left (pow_nonneg hh _) (by linarith only [base])),?_,?_⟩
  · simpa only [mul_right_comm C (z^d) (H^2)] using og
  · rw [pow_add];exact side.trans_eq (by ring)

theorem rest {rent fee γ ε:ℝ}(p:ℕ)(due:fee*rent ≤ γ^p)(sold:1 ≤ fee)(rr:0 ≤ rent)
    (account:F.rent=rent+ε*γ^p):F.rent ≤ (1+ε)*γ^p:=by
  rw [account,add_mul,one_mul]
  exact add_le_add ((le_mul_of_one_le_left rr sold).trans due) le_rfl

end YM.Integration.WilsonOriginalFiledClockMoney
end
