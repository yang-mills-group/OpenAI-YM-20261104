import YM.AllOrder.Laplace.Span
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-!
# Hessian receipt for replacing the curved critical point shift with its linear jet
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Radial Tested MeasureTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff BigOperators Classical
variable {X Y Z:Type}[NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y] [NormedAddCommGroup Z][NormedSpace ℝ Z]
local notation "Ω" => ℝ × Y
section jet
variable {f g : X→ℝ}{u : X→Y}{h : Y→ℝ}{n:ℕ}
-- mostly analytic ω. K,J ext gauges can shrink. needed (ω≥). 
lemma jet_add (hf: ContDiffAt ℝ ω f 0) (hg:ContDiffAt ℝ ω g 0) (x:X):jet (f+g) n x=jet f n x+jet g n x:= by
   rw [jet, jet, jet,iteratedFDeriv_add_apply (hf.of_le le_top) (hg.of_le le_top),_root_.add_apply,mul_add]
lemma jet_two_H (f:X→ℝ)(x:X): jet f 2 x=(2:ℝ)⁻¹ * fderiv ℝ (fderiv ℝ f) 0 x x:= by rw [jet,iteratedFDeriv_two_apply]; norm_num [Nat.factorial]
lemma zero_first (f:X→ℝ) (x:X): jet f 1 x=fderiv ℝ f 0 x:= by simp [jet,iteratedFDeriv_one_apply]
lemma jet_two_C (hu:ContDiffAt ℝ ω u 0) (hv:ContDiffAt ℝ ω h 0) (he:u 0=0) (hg:fderiv ℝ h 0=0) (x:X): jet (h ∘ u) 2 x=jet h 2 (fderiv ℝ u 0 x):=by
 let A:= ContinuousLinearMap.toSpanSingleton ℝ x; let L:= u ∘ A
 have hx:L 0=0:=by simp [L,A,he]
 have ht: HasDerivAt L (fderiv ℝ u 0 x) 0:= by
    have ht:=(((show DifferentiableAt ℝ u (A 0) from (by rw [_root_.map_zero]; exact hu.differentiableAt (by simp))).hasFDerivAt).comp_hasDerivAt (0:ℝ) (show HasDerivAt A x 0 from by change HasDerivAt (fun t:ℝ=> t • x) _ _; simpa only [one_smul] using (((hasDerivAt_id' (0:ℝ)).smul_const x)))); rwa [_root_.map_zero] at ht
 -- edit
 rw [homogeneous_derivative (h ∘ u) x 2 (((he.symm ▸ hv).comp _ hu).of_le le_top)]
 change _⁻¹ * iteratedDeriv 2 (h ∘ L) 0= _
 rw [iteratedDeriv_vcomp_two (hx.symm ▸ hv.of_le (by simp)) _ , hx,hg,_root_.zero_apply,add_zero,jet, ht.deriv]
 exact (show ContDiffAt ℝ (↑(2:ℕ)) u (A 0) from (by rw [_root_.map_zero]; exact hu.of_le le_top)).comp _ A.contDiff.contDiffAt
end jet

section centering
variable (F:X × Y→ℝ) (ρ:X→Y)
def curvature (F : X × Y →ℝ) (x:X)(z:Y) := jet F 2 (x, z)
structure Steered (F:X×Y→ℝ)(ρ:X→Y):Prop where
   hard: ContDiffAt ℝ ω F 0
   root : F 0=0
   quiet : fderiv ℝ F 0=0
   map0 : ρ 0=0
   shape : ContDiffAt ℝ ω ρ 0
   gauge x y: curvature F x (fderiv ℝ ρ 0 x+y)= curvature F x (fderiv ℝ ρ 0 x) + curvature F 0 y
   stand y : y≠0→0 < curvature F 0 y
-- gauge by derivatives
lemma curvature_separate (hf:ContDiffAt ℝ ω F 0)(h:ContDiffAt ℝ ω ρ 0)(h₀:ρ 0=0)(ht : ∀ (y:Y),∀ᶠ x in 𝓝 (0:X), fderiv ℝ F (x,ρ x) (0,y)=0)(x:X)(y:Y): curvature F x (fderiv ℝ ρ 0 x+y)=curvature F x (fderiv ℝ ρ 0 x) + curvature F 0 y:= by
  let a:= (x,fderiv ℝ ρ 0 x); let b:= ((0:X),y); let C : X→ X×Y:=fun x=>(x,ρ x)
  let T:= fderiv ℝ F
  let f x:= T (C x)
  have hc:C 0=0:= Prod.ext rfl h₀
  have hcL:HasFDerivAt C ((ContinuousLinearMap.id ℝ X).prod (fderiv ℝ ρ 0)) 0:= (hasFDerivAt_id _).prodMk ((h.differentiableAt (by simp)).hasFDerivAt)
  have htL:HasFDerivAt T (fderiv ℝ T 0) (C 0) := by rw [hc]; exact ((hf.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hm := htL.comp 0 hcL
  have hk:= hm.clm_apply (hasFDerivAt_const b (0:X)) -- order
  have hb : HasFDerivAt (fun x:X=> f x b) 0 0:= (hasFDerivAt_const (𝕜:=ℝ) (0:ℝ) (0:X)).congr_of_eventuallyEq (ht y)
  have he:fderiv ℝ T 0 a b=0:= by have he:= DFunLike.congr_fun (hk.unique hb) x; rw [_root_.add_apply,ContinuousLinearMap.comp_apply,_root_.zero_apply,map_zero,zero_add] at he; exact he
  unfold curvature; rw [show (x,fderiv ℝ ρ 0 x+y) = a+b by simp [a,b]]; simp_rw [jet_two_H,map_add,_root_.add_apply]; change (2:ℝ)⁻¹ * ((fderiv ℝ T 0 a a + fderiv ℝ T 0 b a)+(fderiv ℝ T 0 a b + fderiv ℝ T 0 b b))=_; rw [show fderiv ℝ T 0 b a=fderiv ℝ T 0 a b from (ContDiffAt.isSymmSndFDerivAt hf le_top).eq b a,he]; unfold T a b; ring -- orientation order check
end centering
end YM.AllOrder.Laplace
