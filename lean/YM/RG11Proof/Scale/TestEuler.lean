import YM.RG11Proof.Scale.Move
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Reading the Euler derivative under a separated integral

Uses a swept COMPACT SUBSET of conf (not just an unseparated spacetime
bound!) around a finite u. Implied dependencies on compact modulus/norm of K
are harmless for this formal-shape criterion but not automatically uniform on
regulator or collision/probe windows. -/
set_option autoImplicit false
set_option maxHeartbeats 150000
noncomputable section
namespace YM.RG11.Scale
open MeasureTheory Set Function Filter TopologicalSpace
open scoped Topology ContDiff BigOperators Classical
variable {n:ℕ}

theorem near_gust (u:ℝ)(f:Test n)(x:Points n): HasDerivAt (fun a:ℝ=> compress n a f x) (blows n (compress n u f) x) u:=by
   let g:=compress n u f
   have he : HasDerivAt (fun a:ℝ=>compress n a g x) (blows n g x) (u-u):= by rw [sub_self]; exact gust ..
   have h := he.scomp (h:=fun x:ℝ=> x-u) u (hasDerivAt_id' u |>.sub_const u)
   -- intermediate derivative at u-u=0, rewrite
   simp only [one_smul] at h
   convert! h using 1
   funext a
   rw [Function.comp_apply,compress_both,sub_add_cancel]

-- commute generator at another u (from both)? derivative as compress u on blows n f u
 theorem commute (u:ℝ)(f:Test n): compress n u (blows n f)=blows n (compress n u f) :=by
  apply TestFunction.ext; intro x
  have hb (b:ℝ): compress n u (compress n b f)=compress n b (compress n u f):=by rw [compress_both,compress_both,add_comm b]
  let X:=wide u • x
  have h := (gust f X).const_mul (jac n u)
  have he : (fun b:ℝ=> jac n u*compress n b f X)=fun b=> compress n b (compress n u f) x:=funext fun b=> congrArg (fun (f:Test n)=> f x) (hb b)
  change HasDerivAt (fun b:ℝ=>jac n u * compress n b f X) ((jac n u)*(blows n f X)) 0 at h
  rw [he] at h; exact HasDerivAt.unique h (gust ..)

-- swept compact over finite interval
private def sweep (s:Set ℝ)(t:Test n) := (fun z: ℝ × Points n=>wide (-z.1) • z.2) '' (s ×ˢ tsupport t)
private theorem admitted {s:Set ℝ}{t:Test n}:sweep s t ⊆ conf n :=by
  rintro y ⟨x,h,rfl⟩; exact scales_conf.mpr (t.tsupport_subset h.2)

private theorem joint_e {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V](f:V→ℂ)(h:Continuous f)(k: ℕ) : Continuous (fun p:ℝ×V=> (↑(wide p.1):ℂ)^k * f (wide p.1 • p.2)) :=by
   unfold wide; fun_prop

 theorem joint (f:Test n): Continuous (fun z:ℝ × Points n=> compress n z.1 f z.2):=joint_e f f.continuous _

 theorem GaugeEuler {K: Points n→ℂ}(HK:ContinuousOn K (conf n))(f:Test n)(b:ℝ): HasDerivAt (fun u:ℝ=>(compress n u f).applyTo K) ((compress n b (blows n f)).applyTo K) b:=by
   let s:=Metric.closedBall b 1
   have hs : s∈𝓝 b:=Metric.closedBall_mem_nhds b one_pos
   let F':= fun u:ℝ=>fun x:Points n=>compress n u (blows n f) x*K x
   let F:= fun u:ℝ=>fun x:Points n=>compress n u f x*K x
   let L:=sweep s (blows n f)
   have hb : IsCompact L:= ((isCompact_closedBall b 1).prod ((blows n f).hasCompactSupport)).image (by unfold wide; fun_prop)
   obtain ⟨C,hC⟩:= (IsCompact.prod (isCompact_closedBall b 1) hb).exists_bound_of_continuousOn
      (f:=fun p:ℝ × Points n=> F' p.1 p.2) ((joint _).continuousOn.mul (HK.comp continuous_snd.continuousOn (fun _ ht=> admitted ht.2)))
   let bound:Points n→ℝ:=L.indicator (fun _=>C)
   have hl : Integrable bound:= (integrable_indicator_iff hb.measurableSet).mpr (integrableOn_const hb.measure_lt_top.ne)
   refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=volume) (F:=F) (F':=F') hs
      (Eventually.of_forall (fun u=> ((compress n u f).smearing HK).1)) ((compress n b f).smearing HK)
      (((compress n b (blows n f)).smearing HK).1) (Eventually.of_forall (fun x u hu=>?_)) hl (Eventually.of_forall (fun x u _=>?_))).2
   · by_cases h:x∈L
     · unfold bound; rw [indicator_of_mem h]; exact hC (u,x) ⟨hu,h⟩
     have he : (blows n f) (wide u • x)=0:= image_eq_zero_of_notMem_tsupport (fun hm=> h ⟨(u,wide u • x),⟨hu,hm⟩,by simp [smul_smul,wide,Real.exp_neg]⟩)
     simp only [bound,F',compress_apply,he,mul_zero,zero_mul, norm_zero,indicator_of_notMem h,le_refl]
   unfold F'
   rw [commute u f]; exact (near_gust u f x).mul_const (K x)
end YM.RG11.Scale
