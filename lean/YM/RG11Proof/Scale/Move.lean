import YM.Euclid.Test
import YM.RG11Proof.Scale.Beam
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
/-!
# Euclidean Tests under dilation and Euler

Use n all arities incl zero, `conf n` in the release. Jacobian counted on
the FULL tuple (integrating Points n). Not usual τ in Ward formalism unless
show its reduction to these tests. Euler with no field dimensions subtracted
(the CS comparison in `Scale/CS` subtracts them *afterwards*). Joint profiles,
not just simple tensors or point clouds.
-/
set_option autoImplicit false
set_option maxHeartbeats 60000
noncomputable section
namespace YM.RG11.Scale
open MeasureTheory Set Function Filter TopologicalSpace
open scoped Topology ContDiff BigOperators Classical

variable {n:ℕ}

abbrev depth (n:ℕ):ℕ:=Module.finrank ℝ (Points n)

theorem four_n (n:ℕ): depth n=n*4:=by
   unfold depth; rw [Points.flatten.toLinearEquiv.finrank_eq]; simp [Axis]

def wide(u:ℝ):ℝ:=Real.exp u
def jac (n:ℕ)(u:ℝ):ℂ:= (wide u:ℝ)^depth n

private theorem scales_id(u:ℝ)(x:Points n):wide (-u) • wide u • x=x:=by simp [smul_smul,wide,Real.exp_neg]

theorem scales_conf {u:ℝ}{x:Points n}: wide u • x∈conf n ↔ x∈conf n:=by
 constructor
 · intro h i j he; apply h; change wide u • (x i) = wide u • (x j); rw [show x i=x j from he]
 intro h i j he; apply h; change wide u • (x i)=wide u • (x j) at he
 change x i=x j
 rw [← one_smul ℝ (x i),← one_smul ℝ (x j),← inv_mul_cancel₀ (Real.exp_ne_zero u),mul_smul,mul_smul]; rw [show Real.exp u • x i=Real.exp u • x j from he]

private theorem shrink_image (f:Test n)(u:ℝ) :
   tsupport (fun x:Points n=>jac n u * f (wide u • x)) ⊆ (fun x:Points n=>wide (-u) • x) '' tsupport f:=by
   refine closure_minimal ?_ ((f.hasCompactSupport.image (continuous_id.const_smul (wide (-u)))).isClosed)
   rintro x hx
   refine ⟨wide u • x, subset_closure (show _∈support f from ?_),scales_id u x⟩
   intro h; apply hx
   change jac n u * f (wide u • x)=0; rw [show f _=0 from h,mul_zero]

def compress (n:ℕ)(u:ℝ)(f:Test n):Test n where
  toFun x:= jac n u * f (wide u • x)
  contDiff':=contDiff_const.mul (f.contDiff.comp ((contDiff_id (𝕜:=ℝ) (E:=Points n)).const_smul (wide u)))
  hasCompactSupport':=IsCompact.of_isClosed_subset (f.hasCompactSupport.image (continuous_id.const_smul (wide (-u)))) (isClosed_tsupport _) (shrink_image f u)
  tsupport_subset':=fun _ h=>by
    obtain ⟨x,hx,rfl⟩:=shrink_image f u h; exact scales_conf.mpr (f.tsupport_subset hx)

@[simp] theorem compress_apply (u:ℝ)(f:Test n)(x):compress n u f x=jac n u*f (wide u • x):=rfl

@[simp] theorem compress_zero : compress n 0=id:=by funext f; ext x; simp [wide,jac]

theorem compress_both (u s:ℝ)(f:Test n):compress n u (compress n s f) = compress n (u+s) f:=by
  apply TestFunction.ext; intro x
  simp only [compress_apply,smul_smul,add_comm u,jac,wide,Real.exp_add]
  simp only [Complex.ofReal_mul, mul_pow,mul_assoc]; rw [mul_left_comm]

/-- Scale point, rather than joint test, according to anchored-X reporting
convention. No algebraic structure/covariance hypotheses on K. -/
theorem reads_compress (K:Points n→ℂ)(u:ℝ)(f:Test n):
   (compress _ u f).applyTo K=f.applyTo (fun x=>K (wide (-u) • x)):=by
  let H(x:Points n):= f x * K (wide (-u) • x)
  have he : (fun x=>compress _ u f x * K x)=fun x=> jac n u * H (wide u • x):=funext fun x=>by simp_rw [compress_apply,mul_assoc,H,scales_id u x]
  unfold Test.applyTo; rw [he, integral_const_mul,Measure.integral_comp_smul_of_nonneg volume H (wide u) (hR:=(Real.exp_pos u).le)]
  unfold jac depth
  rw [Complex.real_smul,←mul_assoc,← Complex.ofReal_pow,←Complex.ofReal_mul,wide,mul_inv_cancel₀ (pow_ne_zero _ (Real.exp_ne_zero u)),Complex.ofReal_one,one_mul]

def breeze (f:Test n)(x:Points n):= (depth n:ℂ)*f x+fderiv ℝ (f: Points n→ℂ) x x

-- tsupport local
private theorem stay (f:Test n):tsupport (breeze f)⊆ tsupport f:=by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x h
  by_contra he
  apply h
  have ht: x∉tsupport (fderiv ℝ (f:Points n→ℂ)) := fun a=>he (tsupport_fderiv_subset ℝ a)

  change breeze f x=0
  simp only [breeze,image_eq_zero_of_notMem_tsupport he,image_eq_zero_of_notMem_tsupport ht,zero_apply,mul_zero,zero_add]

def blows (n:ℕ)(f:Test n):Test n where
  toFun:=breeze f
  contDiff':= (contDiff_const.mul f.contDiff).add ((f.contDiff.fderiv_right (by simp)).clm_apply contDiff_id)
  hasCompactSupport':=f.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (stay f)
  tsupport_subset':=(stay f).trans f.tsupport_subset

@[simp] theorem blows_apply (f:Test n)(x): blows n f x=breeze f x:=rfl

private theorem gust_e {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V](f:V→ℂ)(vf:ContDiff ℝ ∞ f)(x : V)(n:ℕ): HasDerivAt (fun u:ℝ=> (↑(wide u):ℂ)^n * f (wide u • x)) ((n:ℂ)*f x+fderiv ℝ f x x) 0:=by
   let D:= fun u : ℝ=> wide u • x
   have hD:HasDerivAt D x 0:=by
     have hw : HasDerivAt wide 1 (0:ℝ):=Real.exp_zero ▸ Real.hasDerivAt_exp (0:ℝ)
     simpa only [D,smul_eq_mul,one_smul] using hw.smul_const (x)
   have hh : HasDerivAt (fun u=> f (D u)) (fderiv ℝ (f:V→ℂ) x x) 0:=by
     have he : D 0=x:=by simp [D,wide]
     have hk:= ((vf.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=D 0)).comp_hasDerivAt 0 hD
     rw [he] at hk; exact hk
   have hj : HasDerivAt (fun u:ℝ=>(↑(wide u):ℂ)^n) (n:ℂ) 0:=by
     have hw : HasDerivAt wide (Real.exp 0) 0:=Real.hasDerivAt_exp _
     have he := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hw.pow (n))
     simpa [wide,Function.comp_def,Complex.real_smul] using he
   have hprod:=hj.mul hh
   simp only [D,wide,Real.exp_zero,Complex.ofReal_one,one_pow,one_smul,one_mul] at hprod
   exact hprod
/-- Euler as derivative of joint test at u=0; applying to array derivative
requires its continuity/cost in a test LF system or else proof of integration
argument (`GaugeEuler`). -/
theorem gust (f:Test n)(x:Points n): HasDerivAt (fun u:ℝ=>compress n u f x) (blows n f x) 0:=gust_e f f.contDiff x _
end YM.RG11.Scale
