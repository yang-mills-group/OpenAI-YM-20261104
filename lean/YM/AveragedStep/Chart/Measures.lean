import YM.AveragedStep.Chart.Gap
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.Cuff
open RG Lattice Filter Function Precision Set Metric MeasureTheory
open scoped Topology Matrix.Norms.Frobenius ENNReal BigOperators Classical ContDiff
variable {G:Gauge}{P:Patch}{K:KernelChoices}{A:ChartRatio G}(Q:Cuff P K A)(H:LocalRatio A)

def horizon : Set G.Color:= closedBall 0 (2*Q.width)
omit H in
lemma withinH : Q.horizon ⊆ Metric.ball 0 A.radius:=closedBall_subset_ball (by linarith [Q.within,Q.active])
include H
lemma recoil : Measure.map G.lieExp ((volume.restrict Q.horizon).withDensity (fun z:G.Color=>ENNReal.ofReal (A.scale*A.J z)))= G.probHaar.restrict Q.core:=by
  have he:=Measure.restrict_map G.lieExp_cont.measurable Q.core_meas (μ:=((volume.restrict (Metric.ball 0 A.radius)).withDensity (fun z:G.Color=>ENNReal.ofReal (A.scale*A.J z))))
  have hf:=Q.withinH
  have hz : G.lieExp ⁻¹' Q.core ∩ ball 0 A.radius=Q.horizon:=by
    ext u; constructor
    · rintro ⟨⟨z,hz,h⟩,ht⟩
      change z∈ Q.horizon at hz
      exact H.inject (hf hz) ht h ▸ hz
    exact fun hh=>⟨⟨u,hh,rfl⟩,hf hh⟩
  rw [H.actual,Measure.restrict_restrict_of_subset (show Q.core ⊆ G.lieExp '' ball 0 A.radius from Set.image_mono hf),restrict_withDensity (G.lieExp_cont.measurable Q.core_meas),Measure.restrict_restrict (G.lieExp_cont.measurable Q.core_meas),hz] at he
  exact he.symm
lemma reduction {f:G.El→ℝ}(h:Measurable f)(hC: ∀ x∉ Q.core,f x=0):
    (∫ x,f x ∂G.probHaar)= A.scale * ∫ x in Q.horizon,f (G.lieExp x)*A.J x:=by
  calc
    _ = ∫ x in Q.core,f x∂G.probHaar:= (setIntegral_eq_integral_of_forall_compl_eq_zero hC).symm
    _ = _:= by
      rw [← Q.recoil H, integral_map G.lieExp_cont.measurable.aemeasurable h.aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul (H.borel.const_mul _).ennreal_ofReal]
      swap; · exact Eventually.of_forall fun _=> ENNReal.ofReal_lt_top
      rw [← integral_const_mul]
      apply setIntegral_congr_ae measurableSet_closedBall
      filter_upwards with x hx; rw [ENNReal.toReal_ofReal (mul_pos H.scale (H.pos x ((Q.withinH) hx))).le,smul_eq_mul]; ring

/- smooth cut in exponential chart. evaluating in the complement returns
zero. Do NOT assume smooth global gauge slice; only differentiate in chart.
-/
omit H
def trigger : ContDiffBump (0:G.Color):=⟨Q.width/8,Q.width/2,by have :=Q.active; positivity,by linarith [Q.active]⟩
-- group gate and derivative reader

def ticket (x:G.El):ℝ:= if x∈Q.core then Q.trigger (Q.logC x) else 0
def incline (v:G.Color) (x:G.El):ℝ:= if x∈Q.core then fderiv ℝ (Q.trigger:G.Color→ℝ) (Q.logC x) v else 0
lemma ticket_paid : Envelope Q.ticket:=by
 unfold ticket
 exact Envelope.piece Q.core_meas ⟨Q.trigger.continuous.measurable.comp Q.log_meas,1,fun u=> by rw [Real.norm_of_nonneg (Q.trigger.nonneg)]; exact Q.trigger.le_one⟩ (Envelope.const _)
lemma incline_bound (v:G.Color):∃ C:ℝ,∀ x, ‖fderiv ℝ (Q.trigger:G.Color→ℝ) x v‖≤ C:=by
 let F (x:G.Color):= (fderiv ℝ (Q.trigger:G.Color→ℝ) x) v
 have he : Continuous F:=(Q.trigger.contDiff.continuous_fderiv (n:=∞) (by simp)).clm_apply continuous_const -- m arg wrong
 obtain ⟨C,Hc⟩:= (isCompact_closedBall (0:G.Color) Q.trigger.rOut).exists_bound_of_continuousOn he.continuousOn
 refine ⟨max C 0,fun x=>?_⟩
 by_cases h:x∈ tsupport Q.trigger
 · rw [Q.trigger.tsupport_eq] at h; exact (Hc x h).trans (le_max_left ..)
 rw [fderiv_of_notMem_tsupport (𝕜:=ℝ) h, zero_apply,norm_zero]; exact le_max_right ..
lemma incline_env (v:G.Color): Envelope (Q.incline v):= by
 unfold incline
 obtain ⟨C,H⟩:=Q.incline_bound v
 refine Envelope.piece Q.core_meas ⟨((Q.trigger.contDiff.continuous_fderiv (n:=∞) (by simp)).clm_apply continuous_const).measurable.comp Q.log_meas,C,fun x=> H _⟩ (Envelope.const _)
lemma tickets {x:G.Color}(h:x∈Q.horizon)(v:G.Color):
    Q.ticket (G.lieExp x)=Q.trigger x∧ Q.incline v (G.lieExp x)=fderiv ℝ (Q.trigger:G.Color→ℝ) x v:= by
 have hp:G.lieExp x∈Q.core:=⟨x,h,rfl⟩
 unfold ticket incline; rw [if_pos hp,if_pos hp,Q.wind_id (by simpa [horizon] using h)]; exact ⟨rfl,rfl⟩
lemma detected {x:G.El}(h:Q.ticket x ≠0): x∈Q.core∧ ‖Q.logC x‖<Q.width/2:=by
 unfold ticket at h; split at h; next hh=>
   refine ⟨hh,?_⟩; change Q.logC x∈ Function.support Q.trigger at h
   rw [Q.trigger.support_eq,mem_ball_zero_iff] at h; exact h
 exact False.elim (h rfl)
lemma lost {v:G.Color}{x:G.El}(h: Q.incline v x≠0): x∈Q.core ∧ ‖Q.logC x‖≤Q.width/2:=by
 unfold incline at h; split at h; next hh=>
   refine ⟨hh,?_⟩; by_cases he: Q.logC x ∈ tsupport Q.trigger; rw [Q.trigger.tsupport_eq,mem_closedBall,dist_zero_right] at he; exact he
   rw [fderiv_of_notMem_tsupport (𝕜:=ℝ) he, zero_apply] at h; contradiction
 exact False.elim (h rfl)
lemma ticket_one:Q.ticket 1=1:=by
 rw [←G.mat_lieExp_zero]; have ht:0∈ Q.horizon:= mem_closedBall_self (by have :=Q.active; positivity)
 rw [(Q.tickets ht 0).1]; exact Q.trigger.one_of_mem_closedBall (mem_closedBall_self (by have :=Q.active; simp only [trigger]; positivity))
-- later log_bought to control ticket/der failures by gates
end YM.AveragedStep.Cuff
