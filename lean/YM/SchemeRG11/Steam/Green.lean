import YM.SchemeRG11.Steam.Dash
/-!
Explicit massless off-origin lines.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster MSbar
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace

lemma tint_i (l : List Axis) {x : E4} (hx : x≠0) : IntegrableOn (fun t=> tint l t x) openZen := by
  have hh : IntegrableOn (fun t=> (tint l t x:ℂ)) openZen:= by simp_rw [melt 1]; exact (hemp one_pos l).soluble hx
  exact hh.re
lemma costs (l : List Axis) {K : Set E4} (hk : IsCompact K) (hl : 0∉K) :
    ∃ C>0, ∀ x∈K, ∀ t>0, ‖tint l t x‖ ≤ C*Hearth.coat t := by
  obtain ⟨C,hC,c⟩:= (hemp one_pos l).medal hk hl
  exact ⟨C,hC,fun x hx t ht=> by rw [← Complex.norm_real,melt 1]; exact c x hx t ht⟩

lemma redact {x : E4} (hx : x≠0) : (∫ t in openZen,gauze t x)=Green x := by
  have hx':=norm_pos_iff.mpr hx
  let c := ‖x‖^2/4
  have hc:0<c:=by unfold c; positivity
  let F := fun t:ℝ=> Green x*Real.exp (-c*t⁻¹)
  have hm {t : ℝ} (ht : 0<t): HasDerivAt F (gauze t x) t := by
     convert! ((((hasDerivAt_inv ht.ne').const_mul (-c)).exp).const_mul (Green x)) using 1
     unfold Green normal gauze base α c; rw [show -((4*t)⁻¹)*‖x‖^2=-(‖x‖^2/4)*t⁻¹ by ring]; field_simp
  let L:=update F 0 0
  have h e (he : 0<e) : L =ᶠ[𝓝 e] F:= Eventually.mono (lt_mem_nhds he) fun t ht=>update_of_ne (ne_of_gt ht) ..
  have heq:= integral_Ioi_of_hasDerivAt_of_tendsto (f:=L) (m:= Green x) (f':=fun t=>gauze t x) ?_ (fun t ht=> (hm ht).congr_of_eventuallyEq (h t ht)) (tint_i [] hx) ?_
  · rw [show L 0=0 from update_self ..,sub_zero] at heq; exact heq
  · refine continuousWithinAt_update_same.mpr ?_
    rw [show Ici (0:ℝ) \ {0}=Ioi 0 by ext x; simp [lt_iff_le_and_ne,eq_comm]]
    simpa only [F,comp_def,Function.comp_apply,mul_zero] using (Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (r:=-c) (by linarith) tendsto_inv_nhdsGT_zero)).const_mul (Green x)
  apply Tendsto.congr' (f₁:=F) ((eventually_gt_atTop 0).mono fun t ht=> Eq.symm (update_of_ne ht.ne' ..))
  have hh:= ((Real.continuous_exp.tendsto (-c*0)).comp (tendsto_inv_atTop_zero.const_mul (-c))).const_mul (Green x)
  simpa only [F,comp_def,mul_zero,Real.exp_zero,mul_one] using hh

lemma pulls (l : List Axis) (a : Axis) (t r:ℝ) (x : E4) :
    HasDerivAt (fun r:ℝ=> tint l t (x+r•basis a)) (tint (a::l) t (x+r•basis a)) r :=
     HasFDerivAt.comp_hasDerivAt r (((series_calm (gauze_diff t) (l.map basis)).differentiable (by simp) _).hasFDerivAt) (drift x (basis a) r)

lemma sculpt (l : List Axis) : ∀ x:E4, x≠0 → (∫ t in openZen,tint l t x)=series Green (l.map basis) x := by
  induction l with
  | nil => exact fun _=> redact
  | cons a l ih =>
     intro x hx
     have hf : ContDiffAt ℝ ∞ (series Green (l.map basis)) x := by
       clear ih; induction l with
       | nil => exact Maxwell.freeSmooth hx
       | cons a l ih => exact grad_smooth a ih (by simp)
     let g := fun r:ℝ=> x+r•basis a
     have hg : g 0=x:=by simp [g]
     have hp : ContDiffAt ℝ ∞ (series Green (l.map basis)) (g 0) := hg.symm ▸ hf
     have hh:= hp.differentiableAt (by simp)|>.hasFDerivAt.comp_hasDerivAt (f:=g) 0 (drift x (basis a) 0)
     obtain ⟨K,hK,he,h⟩:= exists_compact_subset Maxwell.open_away (show g 0 ∈ Maxwell.away from ne_of_eq_of_ne hg hx)
     let s := g⁻¹' K
     have hu : s∈𝓝 0:= (drift x (basis a) 0).continuousAt (mem_interior_iff_mem_nhds.mp he)
     obtain ⟨C,hC,e⟩:=costs (a::l) hK (fun hK=> h hK rfl)
     have hi:= (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=fun r t=> tint l t (g r)) (F':=fun r t=> tint (a::l) t (g r)) (bound:=fun t=> C*Hearth.coat t) hu (Eventually.mono hu fun r hr=> (tint_i l (show g r≠0 from h hr)).aestronglyMeasurable) (tint_i l (hg ▸ hx)) (tint_i _ (hg ▸ hx)|>.aestronglyMeasurable) (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht r hr=> e _ hr t ht) (Hearth.pay_coat.const_mul C) (Eventually.of_forall fun t r _ => pulls l a t r x)).2
     have hv : (fun r:ℝ=>∫ t in openZen,tint l t (g r)) =ᶠ[𝓝 0] series Green (l.map basis) ∘ g:= Eventually.mono hu fun r hr => ih _ (h hr)
     have hs:= hi.unique (hh.congr_of_eventuallyEq hv)
     rw [hg] at hs; exact hs
end YM.SchemeRG11.Steam
