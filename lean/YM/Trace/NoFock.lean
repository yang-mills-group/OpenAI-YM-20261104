import YM.Trace.Fock.Subpower
import YM.Trace.TargetSpectral
/-!
Non-Maxwell-Fock implication in the Hilbert (Weyl relative-local) formulation, for the same trace as in the coincidence and spectral statement. It will need
the log law. No assumption of polynomiality of the trace field. See
`YM.Trace.Shell.Comparison` and `YM.Trace.Shell.comparison_of_full`. Nothing here excludes
abstract net isomorphisms not satisfying the map hypotheses.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Trace
open YM Boundary Real Complex Filter Function Set MeasureTheory Fields
open scoped Pointwise BigOperators Topology InnerProductSpace ENNReal
noncomputable def normTest (f : Test4) : Test4 := Probe.sew (Probe.bar (plus f)) (plus f)
lemma normTest_value (f : Test4) : (⇑(normTest f): E4→ℂ) = Complex.ofReal ∘ (fun p => ‖plus f p‖^2) := funext (fun p:E4=> by rw [normTest, Probe.sews, Probe.bar_at]; simp only [Function.comp_apply,ofReal_pow]; exact RCLike.conj_mul ..)
lemma positive_support (f : Test4) (hf : plus f (0:E4) ≠ 0) : ((support (plus f)) ∩ Mink.inside).Nonempty := by
 have H : Continuous (fun η:ℝ => plus f (η • basis timeAxis)) := (plus f).continuous.comp (continuous_id.smul continuous_const)
 obtain ⟨t,ht,ht'⟩ := (((show ∀ᶠ η:ℝ in 𝓝 0, plus f (η • basis timeAxis)≠0 from by simpa using! ((H.continuousAt (x:=0)).tendsto.eventually (isOpen_ne.mem_nhds (x:=plus f ((0:ℝ) • basis timeAxis)) (by simpa using hf)) )
   ).filter_mono (nhdsWithin_le_nhds)).and (self_mem_nhdsWithin (α:=ℝ) (s:=Ioi 0))).exists
 exact ⟨(t:ℝ) • basis timeAxis,ht,by simpa [Mink.inside] using ht'⟩
lemma integrable_f_norm (A : ℝ) (f : Test4) : Integrable (fun p=> ‖plus f p‖^2) (masslessMeasure A) := by
 have h := (massless_growth A).integrable (masslessMeasure A) (normTest f)
 rw [normTest_value] at h
 exact Integrable.mono h ((plus f).continuous.norm.pow 2|>.aestronglyMeasurable) (.of_forall fun p=>le_of_eq (norm_real _).symm)
lemma positive_test_bound (A : ℝ) (hA : A>0) (f : Test4) (hf : plus f (0:E4)≠0) : (0:ℝ)< ∫ p, ‖plus f p‖^2∂masslessMeasure A := by
 apply integral_pos_iff_support_of_nonneg_ae (ae_of_all _ (by intro; dsimp; positivity)) (integrable_f_norm A _)|>.2
 have hs : support (fun p=> ‖plus f p‖^2)=support (plus f) := by ext x; change ‖plus f x‖^2 ≠ 0 ↔ plus f x≠0; simp
 rw [hs,masslessMeasure, withDensity_apply _ (plus f).continuous.isOpen_support.measurableSet]
 refine (lintegral_pos_iff_support (modelDensity_meas A)).2 ?_
 rw [Measure.restrict_apply ((by (solve | apply MeasurableSet.compl (s:=modelDensity A ⁻¹' {(0: ENNReal)}); exact modelDensity_meas A (measurableSet_singleton _))) : MeasurableSet (Function.support (modelDensity A)))]
 refine ((plus f).continuous.isOpen_support.inter Mink.open_inside).measure_pos volume (positive_support f hf)|>.trans_le (measure_mono (fun p hp=> ⟨?_, hp.1⟩))
 have hc : Mink.m p>0 := (Mink.strict_self p).mp hp.2 |>.2
 have hP := targetNorm_pos hA
 change ENNReal.ofReal (targetNorm A * modelWeight p) ≠ 0
 rw [modelWeight,indicator_of_mem (show p∈Mink.cone from (show ‖spatial p‖<time p from hp.2).le)]
 exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hP (sq_pos_of_pos hc))
lemma scaled_vac_norm {H : Hilbert} (w : Test4→ H) {M : Measure E4} (h : FieldsNorm M w) (f : Test4) {r : ℝ} (hr : 1<r):
    ((logWeight r * ‖w (normalized f r)‖^2:ℝ):ℂ)= ∫ p, normTest f p∂rescaled M r := by
    rw [Complex.ofReal_mul,Complex.ofReal_pow] 
    have hE := inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (w (normalized f r))
    rw [← show _ = (↑‖w (normalized f r)‖:ℂ)^2 from hE,h,rescale_integral M hr,← real_smul]; congr 1; exact congrArg _ (funext (fun p:E4=>by rw [normTest,Probe.sews,Probe.bar_at,plus_normalized _ (by linarith : 0<r)]))
noncomputable def normModel (A : ℝ) (f : Test4) := ∫ p, ‖plus f p‖^2∂masslessMeasure A

variable {G : Gauge} {C : Family G} {S : Table C.book} {o : Extraction.Order}
lemma norm_tests_limit {A : ℝ} (Y : Spec.Final C o S) (hA : 0≤A) (h : LogLaw Y A) (f : Test4) :
   Tendsto (fun r:ℝ=> logWeight r * ‖thetaV Y (meanExact Y) (normalized f r)‖^2) atTop (𝓝 (normModel A f)) := by
   obtain ⟨M,hm,hM,hT,hS,hc,hφ,H⟩ := conditional_distributional Y (meanExact Y) rfl h (masslessMeasure A)
     (massless_shadow _) (fun _ hx=> model_laplace hA hx) (massless_growth _)
   have hφ := (hφ (normTest f)).2
   have HE := hφ.congr' (f₂:=fun r:ℝ=>(↑(logWeight r* ‖thetaV Y (meanExact Y) (normalized f r)‖^2) : ℂ)) ((eventually_gt_atTop (1:ℝ)).mono fun r hr=> by dsimp only; rw [scaled_vac_norm _ hM f hr])
   have hel := continuous_re.continuousAt.tendsto.comp HE
   rw [Tickets_eval (massless_growth _) (normTest f)] at hel
   change Tendsto _ _ (𝓝 (Complex.re _)) at hel
   have h2 : (∫ p, normTest f p∂masslessMeasure A)= ↑(normModel A f) := by
         have e := integral_ofReal (𝕜:=ℂ) (f:=fun p : E4=> (‖plus f p‖)^2) (μ:=masslessMeasure A)
         simpa only [normModel, normTest_value,Function.comp_apply] using! e
   change Tendsto (fun r => Complex.re ((↑(logWeight r * ‖thetaV Y (meanExact Y) (normalized f r)‖^2) : ℂ))) _ _ at hel
   rw [h2,ofReal_re] at hel; exact hel
private lemma subquadratic {f : ℝ→ℝ} (hf : ∀ r, 0≤f r) {P : ℝ} (h : Tendsto (fun r=> logWeight r * (f r)^2) atTop (𝓝 P)) : Tendsto (fun r=> r⁻¹ ^4 * f r) atTop (𝓝 0) := by
    have hlog := tendsto_log_atTop
    let g (t : ℝ) := t⁻¹^4 * f t
    have hv := (h.div_atTop (show Tendsto (fun r:ℝ=> (Real.log r)^2) atTop atTop by simp only [pow_two]; exact hlog.atTop_mul_atTop₀ hlog))
    have hh : Tendsto (fun t=>(g t)^2) atTop (𝓝 0) := Tendsto.congr' (f₁:= fun t:ℝ=> (logWeight t*f t^2) / (Real.log t)^2)
       ((eventually_gt_atTop (1:ℝ)).mono fun t ht=> by dsimp only [g]; unfold logWeight; field_simp [(Real.log_pos (show 1<t from ht)|>.ne')]) hv
    have hg t := show 0≤g t from mul_nonneg (by positivity) (hf t)
    exact (by simpa only [(show ((Real.sqrt ∘ fun t => g t ^2)) = g from funext (fun t=> sqrt_sq (hg t))),Real.sqrt_zero, Function.comp_apply] using! (show ContinuousAt _ _ from Real.continuous_sqrt.continuousAt).tendsto.comp hh)
private lemma suppressed_power (f : ℝ→ℝ) (hf : ∀ r, f r≥0) (C : ℝ) (h : ∀ r≥1, f r ≤ C*r^6) : Tendsto (fun r=>logWeight r*f r) atTop (𝓝 0) := by
   refine squeeze_zero' (.of_forall (fun t=>by change 0 ≤ logWeight t * _; exact mul_nonneg (by unfold logWeight; positivity) (hf t))) (f:=fun r:ℝ=> logWeight r * f r) (g:=fun r=> C*((Real.log r/r)^2)) ?_ ?_
   · filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
     unfold logWeight; change _≤_
     have hv := mul_le_mul_of_nonneg_left (h t (show 1≤t from ht.le)) (positive_weight ht|>.le)
     unfold logWeight at hv; exact hv.trans_eq (by field_simp)
   exact (by simpa using! (((show Tendsto (fun r:ℝ=> Real.log r/r) atTop (𝓝 0) by simpa only [pow_one,mul_one,one_mul,add_zero] using! Real.tendsto_pow_log_div_mul_add_atTop (a:=1) (b:=0) (n:=1) one_ne_zero).pow 2).const_mul C))

open Shell
lemma noComparison_log {m : ℕ} (Y : Spec.Final C o S) {A : ℝ} (H : LogLaw Y A) (hA : A>0)
    (U : Y.action.operators.H →ₗᵢ[ℂ] Shell.Sum m) (hc : Shell.Comparison Y (meanExact Y) U) : False := by
   let f := initial E4
   let v := fockWave Y (meanExact Y) U
   have heq p : ‖v p‖ = ‖thetaV Y (meanExact Y) p‖ := U.norm_map _
   have hs := norm_tests_limit Y hA.le H f
   simp_rw [← heq] at hs
   have hv := subquadratic (fun r=> norm_nonneg _) hs
   obtain ⟨B,hb,hq⟩:=square_subpower f v hc.data initial_CC hv
   exact (positive_test_bound _ hA f (by dsimp only [f]; rw [plus_initial]; exact one_ne_zero)|>.ne') (tendsto_nhds_unique hs (suppressed_power _ (fun r=>sq_nonneg _) B hq))
end YM.Trace
