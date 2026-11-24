import YM.Integration.WilsonOriginalPublicPivotPowers
import YM.Integration.WilsonOriginalPublicFigureIncome

/-! The literal finite K-chart input's unscaled numerical charge. The dated
slot pole is cleared once in the native Figure.amount, and the two physical
age factors are separated before choosing the collar. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
namespace YM.Integration.WilsonOriginalPublicPivotSalary
open Filter Finset Lattice RG Wilson Labels PhysicalNext.Repeat.Legato
open WilsonOriginalPublicTrialInput (vector salary)
open WilsonOriginalPublicFigureIncome (height)
open WilsonOriginalMicroscopicGuardedPage (wrapCost)
open WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G)(d j:Fin 3→ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
  (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))(before:∀a,j a≤K)
  (reg:WilsonOriginalMicroscopicGuardedPageSchool.Indexed R d j target η M Y)
local notation "H" a:max => height R (d a)
local notation "F" a:max => R.family.labels.level (d a)
local notation "v" N:max p:max => vector R d j K target η M Y before reg N p
local notation "age" => R.family.S.scale
local notation "mesh" => R.family.S.a

/-- Only original reporter data occur in this price. There is no K, original
cutoff, period or arbitrary covering lift in its arguments. -/
def fixed (m:ℕ) (a:Fin 3):ℝ:=
  2^(H a)*2*((1+wrapCost R (d a) (j a))*M a)*Real.exp (η*(age m-age (j a)))

theorem original (m N per:ℕ)(live:K<N)(a:Fin 3)(gc:ℝ) (pos:0<gc)(small:gc≤1):
    let s:=Real.log gc⁻¹
    let t:=Real.log (mesh K/mesh m)⁻¹
    (∑b:(F a).Index,‖WilsonOriginalPublicTrialFigure.amount R d gc (v N per) a b‖) ≤
      fixed R d j η M m a*Real.exp (((H a:ℕ):ℝ)*s+η*t):=by
  intro s t
  have p0:0≤gc⁻¹:=inv_nonneg.mpr pos.le
  have z1:1≤gc⁻¹:=(one_le_inv₀ pos).mpr small
  have tol (i:(F a).Index):‖((gc^((F a).grades i).2)⁻¹:ℂ)‖≤(gc⁻¹)^(H a):=by
    have e:((F a).grades i).2≤H a:=le_sup (f:=fun b:(F a).Index=>((F a).grades b).2) (mem_univ i)
    have own:‖((gc^((F a).grades i).2)⁻¹:ℂ)‖=(gc⁻¹)^((F a).grades i).2:=by
      rw [norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos,inv_pow]
    exact own.trans_le (pow_le_pow_right₀ z1 e)
  have bare:=WilsonOriginalPublicPivotRoster.inlet R d j K target η M Y before reg N per live a
  have span:t=age K-age m:=by
    dsimp only [t,Schedule.scale]
    rw [Real.log_inv,Real.log_div (R.family.S.a_pos K).ne' (R.family.S.a_pos m).ne',Real.log_inv,Real.log_inv]
    ring
  have degree:(gc⁻¹)^(H a)=Real.exp (((H a:ℕ):ℝ)*s):=by
    rw [Real.exp_nat_mul,Real.exp_log (inv_pos.mpr pos)]
  have shift:Real.exp (η*(age K-age (j a)))=Real.exp (η*(age m-age (j a)))*Real.exp (η*t):=by
    rw [←Real.exp_add,span];ring_nf
  calc
    _ ≤ ∑b:(F a).Index,‖(v N per) a b‖*(gc⁻¹)^(H a):=by
      apply sum_le_sum;intro b _
      rw [WilsonOriginalPublicTrialFigure.amount,norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [Complex.ofReal_inv,Complex.ofReal_pow] using tol b
    _ = (F a).coeffSize ((v N per) a)*(gc⁻¹)^(H a):= (sum_mul ..).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_right bare (pow_nonneg p0 _)).trans (le_of_eq (by
      rw [salary,WilsonOriginalMicroscopicGuardedReporters.stretch,shift,degree,Real.exp_add]
      unfold fixed
      ring))

/-- A sign or orientation change may be made only on its actual registered
source. This estimate uses exactly the coefficient on the indicated live run. -/
theorem issued (m N per:ℕ)(live:K<N)(a:Fin 3)(gc E:ℝ)(pos:0<gc)(small:gc≤1)
    (booked:fixed R d j η M m a≤Real.exp (E*Real.log gc⁻¹)):
    (∑b:(F a).Index,‖WilsonOriginalPublicTrialFigure.amount R d gc (v N per) a b‖) ≤
      Real.exp ((E+(H a:ℕ))*Real.log gc⁻¹+η*Real.log (mesh K/mesh m)⁻¹):=by
  apply (original R d j K target η M Y before reg m N per live a gc pos small).trans
  apply (mul_le_mul_of_nonneg_right booked (Real.exp_pos _).le).trans
  rw [←Real.exp_add];apply Real.exp_le_exp.mpr;ring_nf;exact le_rfl

end YM.Integration.WilsonOriginalPublicPivotSalary
end
