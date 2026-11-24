import YM.MSbar.Symbol.HolJet
import Mathlib.Analysis.Complex.RemovableSingularity

/-! Shear off constant Laurent numerator. Uniform extension up to the mass-shell point here
(regulator coordinate origin, not momentum origin) for smooth external parameters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Symbol.AH
open Function Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {U:Set ℂ} {f:ℂ × X → ℂ}

-- along regulator coordinate (we often use `U = ball 0 _`)
def peel (f:ℂ × X → ℂ)(p:ℂ × X) := dslope (fun y => f (y,p.2)) 0 p.1
omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
@[simp]lemma peeling_eq (f:ℂ × X→ℂ)(p:ℂ × X): p.1*peel f p=f p - f (0,p.2) := by simpa [peel] using sub_smul_dslope (fun y => f (y,p.2)) 0 p.1

omit [FiniteDimensional ℝ X] in
lemma derivative (h: AH U f){z:ℂ} (hz:z∈U) (x:X): deriv (fun y => f (y,x)) z= diff (1,0) f (z,x):=by
    unfold deriv; change (fderiv ℂ (fun y=> f (y,x)) z |>.restrictScalars ℝ) 1=_; rw [← (h.cr z x hz).fderiv_restrictScalars ℝ]; let F(w:ℂ):= f (w,x)
    have hD: HasFDerivAt F (partialL f (z,x)) z:= ((h.smooth _ hz).differentiableAt (by simp)).hasFDerivAt.comp (f:=fun y=>(y,x)) _ ((hasFDerivAt_id z).prodMk (hasFDerivAt_const x z))
    unfold F at hD; rw [hD.fderiv];rfl
-- difference quotient calculus
include X
lemma peeling (h: AH U f)(hu:IsOpen U)(he:(0:ℂ)∈U): AH U (peel f):=by
    refine ⟨?_,?_⟩; swap
    · intro z x hz; exact ((Complex.differentiableOn_dslope (f:=fun y=>f (y,x)) (hu.mem_nhds he)).mpr (fun y hy=>(h.cr y x hy).differentiableWithinAt)).differentiableAt (hu.mem_nhds hz)
    intro z hz; by_cases hv:z=0
    swap
    · let v := U ∩ ({(0:ℂ)}ᶜ); have hv':z∈v:=⟨hz,hv⟩; have hV : IsOpen v:= hu.inter isOpen_compl_singleton
      let P(x:ℂ×X):= x.1⁻¹; have hP: AH v P:= AH.holomorphic hV (fun y hy=>differentiableWithinAt_id.inv hy.2)
      have hF := hP.mul ((h.upon inter_subset_left).sub (AH.param_tame (h.slice he))); exact (hF.congr (g:=peel f) hV (fun z hz x=> by
         change z⁻¹ * (f _- f _)= dslope _ 0 _; rw [dslope_of_ne _ (show z≠0 from hz.2),slope_def_module]; simp)).uses _ hv'
    subst z; let d:=diff (1,0) f; have hD : AH U d:= h.diff_smooth hu (1,0)
    obtain ⟨D,hF,hG⟩:= hD.uses 0 he
    obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp (inter_mem (hu.mem_nhds he) hG) -- contains U ∩ equalset
    let Y (x:(ℂ×X) × ℝ):= (x.2 • x.1.1,x.1.2)
    let L(x:ℂ×X):= ∫ t in Icc (0:ℝ) 1,D (Y (x,t))
    have H:HasTemperateGrowth (D ∘ Y):= hF.comp (by unfold Y; fun_prop)
    have hL : HasTemperateGrowth L:= by
       let μ:=volume.restrict (Icc (0:ℝ) 1); haveI : IsFiniteMeasure μ:= by unfold μ; infer_instance
       have h:= average_growth (ContinuousLinearMap.mul ℝ ℂ) aestronglyMeasurable_id (ae_restrict_mem (s:=Icc (0:ℝ) 1) measurableSet_Icc) isCompact_Icc (μ:=μ) (integrable_const (1:ℂ)) H
       simpa [Function.comp, L,Y,μ] using h
    refine ⟨L,hL,?_⟩; filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr] with z hz
    funext x; let g(t:ℝ):= t•z; have hg(t:ℝ)(ht:t∈Icc 0 1) : g t∈ball (0:ℂ) r := by
        have hz' : ‖z‖<r:= mem_ball_zero_iff.mp hz; rw [mem_ball_zero_iff]; unfold g; rw [norm_smul,Real.norm_of_nonneg ht.1]; exact lt_of_le_of_lt (mul_le_of_le_one_left (by positivity) ht.2) hz'
    have hU(t:ℝ)(ht:t∈Icc 0 1): g t∈ U:= (hR (hg t ht)).1
    have hD'(t:ℝ)(ht:t∈ Icc 0 1): D (g t,x)=d (g t,x):= Eq.symm (congr_fun (show _=_ from (hR (hg t ht)).2) x) -- maybe need beta
    let G(t:ℝ):= f (g t,x);let v(t:ℝ):= D (g t,x)
    change dslope (fun y=>f (y,x)) 0 z= ∫ t in Icc (0:ℝ) 1,v t
    rcases eq_or_ne z 0 with rfl|hn
    · rw [show v=(fun _=> D (0,x)) from (by ext1 t; simp [v,g]),setIntegral_const,dslope_same,h.derivative he]; simpa [v,g,d,hD' 0 (show 0∈ Icc (0:ℝ) 1 from by simp)] using (show d (0,x)=D (0,x) from by simpa [g] using (hD' 0 (by simp)).symm)
    apply mul_left_cancel₀ hn; rw [show z*dslope _ _ _=f (z,x)-f (0,x) from peeling_eq f (z,x),← integral_const_mul,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one]
    have hG : ∀ t∈ uIcc (0:ℝ) 1, HasDerivAt G (z*v t) t:= by
       rw [uIcc_of_le zero_le_one]; intro t ht; unfold v; rw [hD' t ht]; have hk := (h.smooth (g t,x) (hU t ht)).differentiableAt (by simp)
       unfold d diff; rw [← h.cr_rule (hU t ht) x z] -- pattern maybe fail
       have he': HasDerivAt g z t := by unfold g; simpa using (hasDerivAt_id' t).smul_const z
       exact hk.hasFDerivAt.comp_hasDerivAt t (he'.prodMk (hasDerivAt_const t x))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG ((show Continuous (fun t=>z*v t) from continuous_const.mul (hF.1.continuous.comp (by unfold g; fun_prop : Continuous fun t=>(g t,x)))).intervalIntegrable ..)]
    simp [G,g]
end YM.MSbar.Symbol.AH
