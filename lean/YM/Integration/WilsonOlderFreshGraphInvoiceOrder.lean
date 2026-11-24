import YM.Integration.WilsonOlderFreshGraphInvoiceFace
import YM.Integration.WilsonOlderFreshGraphOrderSalary

/-! Lower the actual derivative/rank charge at the original strip,
without imposing an upper bound on that strip. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphInvoiceOrder
open RG Wilson QuadraticLocal.Earn WilsonOlderFreshGraphInvoiceFace WilsonOlderFreshGraphOrderSalary
variable (G:Gauge)(B:BudgetPoint){K a θ:ℝ}
variable (room:1≤K)(along:0≤a)(good:0<θ)

include good in
private theorem heat (s:ℕ):0≤layers B s θ:=by unfold layers;positivity
include room in
private theorem salary (s:ℕ):0≤WilsonOlderFreshGraphInvoiceFace.stipend G B K s:=
  (pow_nonneg (by norm_num :(0:ℝ)≤2) _).trans (begins G B room s)

include room along good in
theorem escape (s seats:ℕ):
    Real.exp (θ/2) ≤ 16*Invoice.price B K s seats a θ G:=by
  have l0:=heat B good s
  have l1:=salary G B room s
  have common_:1≤common B s seats a θ:=balance B s seats along good
  calc
    _≤(2:ℝ)^(4+span B s)*layers B s θ:=WilsonOlderFreshGraphFactorialTariff.exponential good _
    _=16*((2:ℝ)^(span B s)*layers B s θ):=by rw [pow_add];ring
    _≤16*(common B s seats a θ*(WilsonOlderFreshGraphInvoiceFace.stipend G B K s*layers B s θ)):=
      mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right (begins G B room s) l0).trans
          (le_mul_of_one_le_left (mul_nonneg l1 l0) common_)) (by norm_num)
    _=_:=by rw [group]

include room along good in
theorem controlled (seats:ℕ){s t:ℕ}(bounded:s≤t):
    Invoice.price B K s seats a θ G ≤ 256*(Invoice.price B K t seats a θ G)^3:=by
  have hT:=heat B good t
  have hS:=heat B good s
  have cT:=zero_le_one.trans (balance B t seats along good)
  have ls:=salary G B room s
  have lt:=salary G B room t
  have fare:=escape G B room along good t seats
  have gross:0≤Invoice.price B K t seats a θ G:=by rw [group];exact mul_nonneg cT (mul_nonneg lt hT)
  have doubled:Real.exp θ=(Real.exp (θ/2))^2:=by rw [sq,←Real.exp_add];congr 1;ring
  calc
    _=common B s seats a θ*(WilsonOlderFreshGraphInvoiceFace.stipend G B K s*layers B s θ):=group ..
    _≤common B t seats a θ*(WilsonOlderFreshGraphInvoiceFace.stipend G B K t*(layers B t θ*Real.exp θ)):=
      mul_le_mul (common_le B bounded seats along good)
        (mul_le_mul (monotone G B room bounded) (layers_le B bounded good) hS lt) (mul_nonneg ls hS) cT
    _=Invoice.price B K t seats a θ G*Real.exp θ:=by rw [group];ring
    _≤Invoice.price B K t seats a θ G*(16*Invoice.price B K t seats a θ G)^2:=by
      rw [doubled]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le fare _) gross
    _=_:=by ring

end YM.Integration.WilsonOlderFreshGraphInvoiceOrder
end
