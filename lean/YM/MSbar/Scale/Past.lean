import YM.MSbar.Scale.Transport
import YM.MSbar.Dim.MellinLift
/-! Ultraviolet endpoint. After clearing a sufficient number of Taylor orders, simple
scale evolution by Mellin estimate strictly to right half plane. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale.Flight
open Function Filter Metric Set Complex Symbol MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {f g : Vec} {a:ℂ} {i n:ℕ} {s:ℝ}

-- past in ray-variable (opposite Λ movement). after peeling enough exponents, demand a.re<−1,
-- not necessary otherwise). use minus sign convention
abbrev Land (a:ℂ):= a.re < -1
def weight (a:ℂ): Vec:= fun t=> -((t:ℂ)^(-a-1:ℂ))
def past (a:ℂ)(f:Vec)(x:ℝ) := ∫ t in Icc (0:ℝ) 1, weight a t * f (t*x)
private abbrev μ:= volume.restrict (Icc (0:ℝ) 1)
private local instance : IsFiniteMeasure μ:= by unfold μ; infer_instance
variable (hf:Great f)(hg:Great g)(hl:Land a)
include hf hl
private noncomputable def paired (f:Vec): ℝ × ℝ→ℂ := fun (x,u)=> f (u*x)
omit hf in
lemma desc : 0< (-a-1).re :=by simp; linarith [show a.re < -1 from hl]
omit hf in
lemma goes : Continuous (weight a):= (continuous_ofReal_cpow_const (desc hl)).neg
omit hf in
lemma residue : Integrable (weight a) μ := (goes hl).continuousOn.integrableOn_compact isCompact_Icc
omit hl in
private lemma joint : (paired f).HasTemperateGrowth:= hf.comp (by fun_prop : HasTemperateGrowth (fun x:ℝ × ℝ=>x.2*x.1))
local notation "B" => ContinuousLinearMap.mul ℝ ℂ
lemma int (x:ℝ): Integrable (fun u=>weight a u * f (u*x)) μ:= average_integrable B aestronglyMeasurable_id (ae_restrict_mem (s:=Icc (0:ℝ) 1) measurableSet_Icc) isCompact_Icc (μ:=μ) (residue hl) (joint hf).1.continuous x
lemma growth : Great (past a f):= average_growth B aestronglyMeasurable_id (ae_restrict_mem (s:=Icc (0:ℝ) 1) measurableSet_Icc) isCompact_Icc (μ:=μ) (residue hl) (joint hf)
omit hl in
lemma tall (x t:ℝ) : HasDerivAt (fun y=> f (x*y)) ((x:ℂ)*deriv f (x*t)) t := ((hf.1.differentiable (by simp) (x*t)).hasDerivAt).scomp t (show HasDerivAt (fun y:ℝ=>x*y) x t by simpa using (hasDerivAt_id' t).const_mul x)
omit hl in
lemma wider (x t:ℝ) : HasDerivAt (fun y=> f (y*x)) ((x:ℂ)*deriv f (t*x)) t := by simpa only [mul_comm x] using tall hf x t
lemma derive (x:ℝ): deriv (past a f) x = ∫ u in Icc (0:ℝ) 1, weight a u*((u:ℂ)*deriv f (u*x)):=by
    have ht := average_hasFDeriv B aestronglyMeasurable_id (ae_restrict_mem (s:=Icc (0:ℝ) 1) measurableSet_Icc) isCompact_Icc (μ:=μ) (residue hl) (joint hf).1 x; change HasFDerivAt (past a f) _ _ at ht
    have hv : Integrable (fun u=> (B (weight a u)).comp (partialL (paired f) (x,u))) μ := average_integrable ((B).precompR ℝ) aestronglyMeasurable_id (ae_restrict_mem (s:=Icc (0:ℝ) 1) measurableSet_Icc) isCompact_Icc (μ:=μ) (residue hl) (partialL_smooth (joint hf).1).continuous x
    rw [deriv, ht.fderiv]; simp only [id_eq]; rw [ContinuousLinearMap.integral_apply hv]; refine integral_congr_ae ?_
    filter_upwards with u; change weight a u*partialL _ (x,u) 1= weight a u*_ ; congr! 1; rw [← partialL_fderiv (joint hf).1]; exact (tall hf u x).deriv
lemma commute : past a (flight a f)= flight a (past a f):=by
    funext x; unfold flight; rw [derive hf hl]; change _=a * (∫ t, weight a t*f (t*x) ∂μ) - (x:ℂ) * ∫ t, weight a t*((t:ℂ)*deriv f (t*x)) ∂μ; rw [← integral_const_mul,← integral_const_mul, ← integral_sub]; swap
    · exact (int hf hl x).const_mul a
    rotate_left
    · exact ((show Continuous _ from (goes hl).mul (continuous_ofReal.mul ((deriv_tame_ray hf).1.continuous.comp (show Continuous (fun y:ℝ=> y*x) by fun_prop)))).continuousOn.integrableOn_compact (μ:=volume) isCompact_Icc ).const_mul (x:ℂ) -- goal order
    apply integral_congr_ae; filter_upwards with u; push_cast; ring
lemma solve_left : past a (flight a f)= f:=by
    funext x; let g:ℝ→ℂ:=fun u=>(u:ℂ)^(-a)*f (u*x); let e:ℝ→ℂ:= fun u=>weight a u * flight a f (u*x)
    have hv: 0< (-a).re:=by linarith [desc hl,(show (-a-1).re=(-a).re-1 by simp)]
    have hh: -a ≠ 0:= fun h=>by rw [h] at hv; exact (lt_irrefl _) hv
    have he : Continuous e:= (goes hl).mul ((go hf).1.continuous.comp (show Continuous (fun u:ℝ=>u*x) by fun_prop))
    have hg: Continuous g:= (continuous_ofReal_cpow_const hv).mul (hf.1.continuous.comp (show Continuous (fun u:ℝ=>u*x) by fun_prop))
    have h(u:ℝ)(hu:u∈Ioo (0:ℝ) 1):HasDerivAt g (e u) u:= by
        have hN:(u:ℂ)≠0:= ofReal_ne_zero.mpr (hu.1.ne'); have hP :HasDerivAt (fun t:ℝ=>(t:ℂ)^(-a)) ((-a)*(u:ℂ)^(-a-1)) u:= by simpa using! (((hasDerivAt_id (u:ℂ)).cpow_const (c:=-a) (ofReal_mem_slitPlane.mpr hu.1)).comp_ofReal)
        rw [show e u= (-a)*(u:ℂ)^(-a-1)*f (u*x)+(u:ℂ)^(-a)*((x:ℂ)*deriv f (u*x)) from ?_]; exact hP.mul (wider hf x u)
        unfold e weight flight; push_cast; rw [show (u:ℂ)^(-a)=(u:ℂ)^(-a-1:ℂ)*u from ?_]; ring
        rw [show (u:ℂ)^(-a-1:ℂ)=(u:ℂ)^(-a)/(u:ℂ) from (by rw [cpow_sub _ _ hN,cpow_one])]; field_simp
    unfold past; rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (zero_le_one),intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f':=fun t:ℝ=> weight a t * flight a f (t*x)) zero_le_one hg.continuousOn h (he.intervalIntegrable ..)]; simp [g,hh]
lemma solve_right : flight a (past a f)= f:=by rw [← commute hf hl, solve_left hf hl]
end YM.MSbar.Scale.Flight
