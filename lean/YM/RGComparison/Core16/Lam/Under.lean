import YM.RGComparison.Core16.Silk.Cord
import YM.Extra.MULTISOURCE_TRAJECTORIES.Smooth
/-!
# Outward Hessian for Θ-conditional averaging
Real ℝ field-log Hessian at V (v=0). Under actual group phase reporter's posterior,
 not assuming measure differentiation of branch likelihood! StepData.likelihood
 depends ONLY ON input configuration. Outer Stim.Jets therefore sees a genuine continuous germ
 in *any* external param changes at GAP-coupling. The analytic task of growth when actually
 taking Taylor in that V/g recovered via explicit tested-moment pipeline, not exchanging here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Precision
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

section earn
variable {X Y : Type*}[NormedAddCommGroup X][NormedSpace ℝ X]

abbrev line1 (C:X→ℝ)(u:X) (a:X): ℝ:= fderiv ℝ C u a
abbrev Hess (C:X→ℝ)(u:X): X→L[ℝ] X→L[ℝ] ℝ:=fderiv ℝ (fderiv ℝ C) u
def lend (C:X→ℝ) (a b:X):= Hess C 0 a b

variable {C : X→ℝ}
lemma wander (h:ContDiff ℝ ∞ C) : Differentiable ℝ (fderiv ℝ C) := (h.fderiv_right (m:=∞) (by simp)).differentiable (by simp)
lemma Diff (h:ContDiff ℝ ∞ C): Differentiable ℝ C := h.differentiable (by simp)
lemma faculty (h : ContDiff ℝ ∞ C)(a b:X)(u:ℝ) :
    line1 (u • C) 0 a=u*line1 C 0 a ∧ lend (u • C) a b=u*lend C a b:=by
    simp_rw [lend, line1,Hess,show fderiv ℝ (u • C)=u • fderiv ℝ C from funext fun i=> (((Diff h i).hasFDerivAt.const_smul u).fderiv : _ = u • _)]
    rw [show fderiv ℝ (u • fderiv ℝ C) 0 = _ from ((wander h 0).hasFDerivAt.const_smul u).fderiv]; exact ⟨rfl,rfl⟩
lemma earnings (h:ContDiff ℝ ∞ C)(u v:X) (a:ℝ) :
      let Z:= Real.exp ∘ (a • C)
      line1 Z 0 u=Z 0*(a* line1 C 0 u) ∧ lend Z u v=Z 0*(a^2*line1 C 0 u*line1 C 0 v + a*lend C u v) := by
    let W:= a • C; let H : ContDiff ℝ ∞ W:= h.const_smul a; intro Z
    have hv p:HasFDerivAt Z (Z p • fderiv ℝ W p) p:= (Diff H p).hasFDerivAt.exp
    have hp : fderiv ℝ Z= fun p=> Z p • fderiv ℝ W p:=funext fun p=> (hv p).fderiv
    have ht:=faculty h u v a; have he:=faculty h v u a; unfold line1 lend Hess
    rw [hp]; dsimp only [smul_apply,smul_eq_mul]; change _∧fderiv ℝ (Z • fderiv ℝ W) 0 u v=_
    rw [((hv 0).smul (wander H 0|>.hasFDerivAt)).fderiv]; simp only [add_apply,smul_apply, ContinuousLinearMap.smulRight_apply,smul_eq_mul]; change Z 0 * line1 W 0 u= _ ∧ _
    refine ⟨congr_arg _ ht.1,?_⟩
    change _ * lend W u v + _ * _=_; simp only [←show ∀ i, line1 W 0 i=fderiv ℝ W 0 i from fun _=>rfl]; rw [ht.1,he.1,ht.2]; unfold lend Hess; ring

lemma logH (h:ContDiff ℝ ∞ C)(he :0< C 0)(a b:X):
   lend (fun p=> -Real.log (C p)) a b= line1 C 0 a * line1 C 0 b / C 0^2 - lend C a b / C 0:=by
    let F:=fderiv ℝ C; let D p:=-Real.log (C p); let Y (x:X):= -(C x)⁻¹
    have h0 : fderiv ℝ D =ᶠ[𝓝 (0:X)] fun x=> Y x • F x :=by
       filter_upwards [(h.continuous.continuousAt.eventually (lt_mem_nhds he))] with x hx; change 0<C x at hx; exact ((Diff h x|>.hasFDerivAt.log (ne_of_gt hx)).neg.fderiv.trans (neg_smul ..).symm)
    have B:=((hasFDerivAt_inv he.ne').comp 0 (Diff h 0|>.hasFDerivAt)).neg
    unfold lend Hess line1
    change fderiv ℝ (fderiv ℝ D) 0 a b=_
    rw [(h0.fderiv_eq : fderiv ℝ (fderiv ℝ D) 0=fderiv ℝ (Y • F) 0)]
    change fderiv ℝ (-(Inv.inv ∘ C) • (fderiv ℝ C)) 0 a b=_
    rw [(B.smul (wander h 0|>.hasFDerivAt)).fderiv]; simp only [add_apply, smul_apply, neg_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]; simp only [Pi.neg_apply, Function.comp_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]; ring
end earn

section integral
variable {A B E : Type} [NormedAddCommGroup A][NormedSpace ℝ A][FiniteDimensional ℝ A][NormedAddCommGroup B][NormedSpace ℝ B][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {ι :Type} [MeasurableSpace ι]
    {u:Measure ι} [IsFiniteMeasure u] (p:ι→B)
def pole (v:A×B→E): A→ E:=fun x=> ∫ i,v (x,p i)∂u
variable {p}{K:Set B}{Z:A×B→E}(hm:AEStronglyMeasurable p u)(he:IsCompact K)(hv:∀ i,p i ∈ K)(hZ:ContDiff ℝ ∞ Z)

def branch (Z:A×B→E)(v:A×B):= fderiv ℝ (fun x=> Z (x,v.2)) v.1

omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ E] in
lemma stem_hot (hZ: ContDiff ℝ ∞ Z): ContDiff ℝ ∞ (branch Z):= ContDiff.fderiv (m:=∞) (f:=fun (q : A × B) (x : A)=> Z (x,q.2)) (hZ.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))) contDiff_fst (by simp)
include hm he hv hZ
lemma pole_hot : ContDiff ℝ ∞ (pole (u:=u) p Z) := Extra.Trajectories.integral_smooth hm he hv hZ
-- Full compact parameter window to differentiate. no O density claim from the Hölder generic lemma; scale budgets charged later.
omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ E] in
lemma addition (x:A):Integrable (fun i=>Z (x,p i)) u:=by
    obtain ⟨C,hC⟩:= he.exists_bound_of_continuousOn (f:=fun y=> Z (x,y)) (hZ.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    exact .of_bound ((hZ.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hm) C (Eventually.of_forall fun a=>hC _ (hv a))
omit [FiniteDimensional ℝ E] in
lemma transit : fderiv ℝ (pole (u:=u) p Z) = pole (u:=u) p (branch Z):= by
    funext x
    obtain ⟨C,hC⟩:= ((isCompact_closedBall x 1).prod he).exists_bound_of_continuousOn (stem_hot hZ).continuous.continuousOn
    apply HasFDerivAt.fderiv
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F':=fun x i=>branch Z (x,p i)) (F:=fun x i=>Z (x,p i)) (bound:=fun _=> C) (Metric.closedBall_mem_nhds x zero_lt_one) (Eventually.of_forall fun y=>(addition hm he hv hZ y).aestronglyMeasurable) (addition hm he hv hZ x) (addition hm he hv (stem_hot hZ) x).aestronglyMeasurable (Eventually.of_forall fun a y hy=> hC _ ⟨hy,hv a⟩) (integrable_const _) (Eventually.of_forall fun a y _=> ((hZ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) y).hasFDerivAt)
omit hZ
variable {V:A×B→ℝ}(h:ContDiff ℝ ∞ V)
include h
lemma slope_rule (a:A): line1 (pole (u:=u) p V) 0 a = ∫ i,line1 (fun x=>V (x,p i)) 0 a∂u := by
    unfold line1; rw [transit hm he hv h]; exact ((ContinuousLinearMap.apply ℝ ℝ a).integral_comp_comm (addition hm he hv (stem_hot h) 0)).symm
lemma exactL (a b:A): lend (pole (u:=u) p V) a b=∫ i,lend (fun x=>V (x,p i)) a b∂u := by
    unfold lend Hess; rw [transit hm he hv h, transit hm he hv (stem_hot h)]; let F: ((A→L[ℝ] A→L[ℝ] ℝ))→L[ℝ] ℝ:= (ContinuousLinearMap.apply ℝ ℝ b).comp (ContinuousLinearMap.apply ℝ (A →L[ℝ] ℝ) a); exact (F.integral_comp_comm (addition hm he hv (stem_hot (stem_hot h)) 0)).symm
end integral
end YM.RGComparison.Core16.Lam
