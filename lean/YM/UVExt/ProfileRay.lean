import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Manifesto
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Analytical primitives for complex step inverse parameter with fixed activity values. A primitive is what is multiplied per vertex, not a claim of a holomorphic iterate of arbitrary RG tuples. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.EnergyRay
open Filter Set Function MeasureTheory
open scoped Classical ComplexConjugate Topology BigOperators

/-- Frozen Boltzmann coefficient with optional frozen-coordinate half powers,
  or exponentiated *pure* energy piece with the unit split off. -/
inductive Primitive
 | thermal (c : ℂ) (bill : ℝ) (degree : ℕ)
 | split (bill : ℝ)

namespace Primitive

def run (p:Primitive) (z:ℂ) : ℂ := match p with
  | thermal c bill k => c*Complex.exp (Complex.log z*(k/2) + z*bill)
  | split b => Complex.exp (z*b)-1

def tax : Primitive → ℕ
  | thermal _ _ k => k
  | split _ => 1

@[simp] lemma basic (c:ℂ) (z:ℂ) : (thermal c 0 0).run z = c := by simp [run]
lemma standard (c:ℂ) (g:ℝ) (k:ℕ) (u:ℝ) (hu:0<u) :
    (thermal c g k).run u=c*(Real.sqrt u:ℂ)^k*(Real.exp (u*g):ℂ) := by
 simp only [run]
 rw [Complex.exp_add,mul_assoc, ← Complex.ofReal_log hu.le]
 congr 2
 · norm_cast
   rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hu,← Real.exp_nat_mul]
   simp only [Complex.ofReal_exp]
   congr 1; push_cast; ring
 norm_cast

lemma accepted (p:Primitive) {z:ℂ} (hz:0<z.re) : DifferentiableAt ℂ p.run z := by
 cases p with
 | thermal c b n=>
   exact ((Complex.differentiableAt_log (Or.inl hz)).mul_const _ |>.add ((differentiableAt_id (𝕜:=ℂ)).mul_const (b:ℂ))|>.cexp).const_mul c
 | split b=>
   exact (differentiable_explicit b).differentiableAt
 where
   differentiable_explicit (b:ℝ) : Differentiable ℂ (fun z:ℂ=>Complex.exp (z*(b:ℂ))-1) := (((differentiable_id (𝕜:=ℂ)).mul_const (b:ℂ)).cexp.sub_const _)

lemma thermal_cost (c:ℂ) (q:ℝ) (n:ℕ) (z:ℂ) (hz:0<z.re) :
    ‖(Primitive.thermal c q n).run z‖ = ((Real.sqrt ‖z‖)/(Real.sqrt z.re))^n * ‖(Primitive.thermal c q n).run z.re‖ := by
 have formula {z:ℂ} (hw:0<z.re) : ‖(Primitive.thermal c q n).run z‖=‖c‖*(Real.sqrt ‖z‖)^n*Real.exp (z.re*q) := by
   have hv : 0<‖z‖ := norm_pos_iff.mpr (fun he=>by simp [he] at hw)
   unfold run
   rw [norm_mul,Complex.norm_exp, Complex.add_re,Real.exp_add, mul_assoc]
   congr 2
   · simp only [Complex.mul_re, mul_zero,sub_zero, Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.natCast_re,Complex.log_re, Complex.natCast_im, zero_div]
     rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hv,← Real.exp_nat_mul]; congr 1; ring
   simp
 rw [formula hz,formula (Complex.ofReal_re _ ▸ hz),Complex.ofReal_re,Complex.norm_real, Real.norm_eq_abs,abs_of_pos hz]
 rw [div_pow]
 field_simp

private lemma exp_split (w:ℂ) : Complex.exp w-1 = w*(∫ x:ℝ in 0..1, Complex.exp (w*(x:ℂ))) := by
 rcases eq_or_ne w 0 with (rfl|hw)
 · simp
 rw [integral_exp_mul_complex hw]; simp only [Complex.ofReal_zero, mul_zero,Complex.exp_zero,Complex.ofReal_one, mul_one]; field_simp

/-- Relative-angle comparison, exactly on the half plane, even for large
positive or negative scalar arguments. Would fail for `exp (d + z b)-1`
with an arbitrary real d and b simultaneously nonzero. -/
lemma split_cap (z:ℂ) (hz:0<z.re) (a:ℝ) :
    ‖Complex.exp (z*(a:ℂ))-1‖ ≤ (‖z‖/z.re) * ‖Complex.exp ((z.re:ℂ)*(a:ℂ))-1‖ := by
 let w := z*(a:ℂ); let u := (z.re:ℂ)*(a:ℂ); let f x:=Real.exp (z.re*a*x)
 have hf : Continuous f := by unfold f; fun_prop
 have hm (x:ℝ) : ‖Complex.exp (w*(x:ℂ))‖= f x := by rw [Complex.norm_exp]; simp [w,f]
 have hu (x:ℝ) : Complex.exp (u*(x:ℂ))= (f x:ℂ) := by simp only [u,← Complex.ofReal_mul,← Complex.ofReal_exp,f]
 rw [exp_split (w:=w), exp_split (w:=u), norm_mul,norm_mul]
 simp_rw [hu]
 have hn := intervalIntegral.norm_integral_le_abs_integral_norm (f:=fun x:ℝ=>Complex.exp (w*(x:ℂ))) (a:=(0:ℝ)) (b:=1) (μ:=volume)
 rw [intervalIntegral.integral_ofReal, norm_mul]
 apply le_trans (mul_le_mul_of_nonneg_left hn (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
 simp_rw [hm]
 rw [Complex.norm_real,Real.norm_eq_abs]
 apply le_of_eq
 unfold u; rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz]; simp_rw [Complex.norm_real,Real.norm_eq_abs]; field_simp

lemma angular (p:Primitive) (z:ℂ) (hz:0<z.re) :
    ‖p.run z‖ ≤ (‖z‖/z.re)^p.tax * ‖p.run z.re‖ := by
 cases p with
 | split b=> simpa [run,tax] using split_cap z hz b
 | thermal c q n=>
   rw [thermal_cost c q n z hz,tax]
   apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) _ n) (norm_nonneg _)
   rw [div_le_div_iff₀ (by positivity [Real.sqrt_pos.mpr hz]) hz]
   have hv := (le_abs_self _).trans (Complex.abs_re_le_norm z)
   conv => rhs; rw [← Real.sq_sqrt (norm_nonneg z)]
   conv => lhs; arg 2; rw [← Real.sq_sqrt hz.le]
   have h := Real.sqrt_le_sqrt hv
   nlinarith only [mul_le_mul_of_nonneg_right h (mul_nonneg (Real.sqrt_nonneg z.re) (Real.sqrt_nonneg ‖z‖))]

/-- Physical inverse-square rescaling inside one actual Gaussian integral. No new gauge-field chart. -/
def atm (β z:ℝ) : ℝ := β*z
lemma gstep_mul (β r:ℝ) (hv:0<β) (hr:0<r) :
    ConnectedActivityE6.Coat.gStep (β*r) * Real.sqrt r = ConnectedActivityE6.Coat.gStep β := by
 rw [ConnectedActivityE6.Coat.gStep, ConnectedActivityE6.Coat.gStep,Real.sqrt_mul hv.le]
 field_simp [ne_of_gt (Real.sqrt_pos.mpr hr),ne_of_gt (Real.sqrt_pos.mpr hv)]

private lemma right : IsOpen {z : ℂ| 0<z.re} := isOpen_lt continuous_const Complex.continuous_re
lemma differentiable_run (p:Primitive) : DifferentiableOn ℂ p.run {z|0<z.re} := fun _ he=> (p.accepted he).differentiableWithinAt
end Primitive
end YM.UVExt.EnergyRay
