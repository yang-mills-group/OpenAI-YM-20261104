import YM.Trace.Fock.Cauchy
/-!
The two Cauchy-data distributions on zero time from a tested incoming and outgoing
pair. Lebesgue 3-measure here (after calling `dυ = scalarWeight · dp`, with no point
at the shell origin).
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
namespace YM.Trace.Shell
open YM Boundary MeasureTheory Filter Set Complex Function
open scoped ENNReal Pointwise Topology ContDiff BigOperators InnerProductSpace
variable {N : ℕ}
def bare (A D : Mom→ℂ) (k : Fin 2) (p : Mom) := if k=0 then (A p - D (-p) : ℂ) / (2*‖p‖) else (A p+D (-p))/2
variable {A D : Mom→ℂ} (hA : Control N A) (hD : Control N D)
def invariantBody (A D : Mom→ℂ) (k : Fin 2) (x) := if k=0 then A x-D (-x) else ‖x‖ • (A x + D (-x))
def bareCost (N) (A D : Mom → ℂ) := (∫ x, ‖A x‖ / moment N x ∂ν) + ∫ x, ‖D (-x)‖ / moment N x ∂ν
omit hA hD in
lemma bareCost_nonneg : 0≤bareCost N A D := add_nonneg (MeasureTheory.integral_nonneg fun p=>div_nonneg (norm_nonneg _) (weight_pos ..|>.le)) (MeasureTheory.integral_nonneg fun p=>div_nonneg (norm_nonneg _) (weight_pos ..|>.le))

include hA hD
private lemma invariantBody_ae (k) : AEStronglyMeasurable (invariantBody A D k) ν := by
    unfold invariantBody; split_ifs
    · exact hA.ae.sub hD.reflection.ae
    exact continuous_norm.aestronglyMeasurable.smul (hA.ae.add hD.reflection.ae)
omit hA hD in
private lemma invariantBody_bound (x k) : ‖invariantBody A D k x‖ ≤ ‖A x‖*(1+‖x‖) + ‖D (-x)‖*(1+‖x‖) := by
    unfold invariantBody
    have ht : 1 ≤ 1+‖x‖ := by linarith [norm_nonneg x]
    rw [mul_comm (_:ℝ) (1+‖x‖),mul_comm (_:ℝ) (1+‖x‖),←mul_add]
    split_ifs
    · exact (norm_sub_le ..).trans (le_mul_of_one_le_left (by positivity) ht)
    rw [norm_smul,norm_norm]; exact (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left (norm_add_le ..) (by linarith))

lemma invariantControl (k : Fin 2) (f : Probe Mom) : let x := fun p:Mom => f p * invariantBody A D k p;
    Integrable x ν ∧ ‖∫ p,x p∂ν‖ ≤ (wavePrice f (N+2)) * bareCost N A D := by
    intro F
    let C := wavePrice f (N+2)
    let M (f : Mom→ℂ) (x : Mom) := C * (‖f x‖ / moment N x)
    let D' p := D (-p)
    have hC₁ := hA.integrable.const_mul C; have hC₂ := hD.reflection.integrable.const_mul C
    have hp (p: Mom) : ‖F p‖ ≤ M A p+ M D' p := by
       refine (le_of_eq (norm_mul (f p) (invariantBody A D k p))).trans (mul_le_mul_of_nonneg_left (invariantBody_bound p k) (norm_nonneg (f p)) |>.trans ?_)
       calc ‖f p‖ * (‖A p‖*(1+‖p‖)+‖D (-p)‖*(1+‖p‖)) = (1+‖p‖)*‖f p*A p‖ + (1+‖p‖)*‖f p*D' p‖ := by dsimp [D']; rw [norm_mul,norm_mul]; ring
            _ ≤ _ := add_le_add (bounded_window f N A p) (bounded_window f N D' p)

    have hc := (hC₁.add hC₂).mono' (f.continuous.aestronglyMeasurable.mul (invariantBody_ae hA hD k)) (ae_of_all _ hp)
    exact ⟨hc,(norm_integral_le_integral_norm ..).trans ((integral_mono hc.norm (hC₁.add hC₂) hp).trans_eq (by simp only [Pi.add_apply]; dsimp [bareCost]; change (∫ p:Mom, (C * _ + C * _)∂ν)= _; rw [integral_add hC₁ hC₂, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← mul_add]))⟩
omit hA hD in
lemma body_density (x : Mom) (hx : x≠0) (k) : (scalarWeight x) • invariantBody A D k x= bare A D k x := by
    have ht := norm_ne_zero_iff.mpr hx
    unfold invariantBody bare scalarWeight; split_ifs <;> simp only [Complex.real_smul] <;> push_cast <;> (field_simp [ht]; try ring)
lemma body_mask (f : Probe Mom) (k) : (fun x=> (ENNReal.ofReal (scalarWeight x)).toReal • (f x * invariantBody A D k x)) =ᶠ[ae (volume:Measure Mom)] (fun x=> f x * bare A D k x) := by
     have he : ∀ᵐ x : Mom, x≠0 := ae_iff.mpr (by simp only [not_not]; exact measure_singleton _)
     apply he.mono (fun x hx=> ?_)
     dsimp only
     rw [ENNReal.toReal_ofReal (scalar_pos _), ← mul_smul_comm,body_density x hx]

lemma bare_integrable (k : Fin 2) (f : Probe Mom) : Integrable (fun x=>f x* bare A D k x) (volume:Measure Mom) := by
     have ht (x : Mom) := ENNReal.toReal_ofReal (scalar_pos x) -- simp only ofReal
     have hv := integrable_withDensity_iff_integrable_smul' (μ:=(volume:Measure Mom)) (f:=ENNReal.ofReal ∘ scalarWeight) (ENNReal.measurable_ofReal.comp scalar_meas)
         (g:=fun p => f p * invariantBody A D k p) (by simp)
     exact (integrable_congr (body_mask hA hD f k)).1 (hv.1 (invariantControl hA hD k f|>.1))
lemma exchangeBody (k : Fin 2) (f : Probe Mom) : (∫ x,f x * invariantBody A D k x ∂ν) = ∫ x:Mom, f x * bare A D k x := by
     unfold ν; rw [integral_withDensity_eq_integral_toReal_smul (ENNReal.measurable_ofReal.comp scalar_meas) (by simp)]
     exact integral_congr_ae (body_mask hA hD f k)

include hA hD in
lemma bounded_bare : ∀ k : Fin 2, ∀ (f : Probe Mom), ‖∫ x:Mom, f x * bare A D k x‖ ≤ wavePrice f (N+2) * bareCost N A D := fun k f=> by rw [← exchangeBody hA hD k f]; exact (invariantControl hA hD k f).2
noncomputable def bareLinear (k : Fin 2) : Probe Mom →ₗ[ℂ] ℂ := {
    toFun f := ∫ x:Mom, f x * bare A D k x
    map_add' x y := by simp only [add_apply,add_mul]; exact MeasureTheory.integral_add (bare_integrable hA hD k x) (bare_integrable hA hD k y)
    map_smul' c x := by simp only [smul_apply,smul_mul_assoc]; exact MeasureTheory.integral_smul _ _ }
noncomputable def bareCLM (k : Fin 2) : Probe Mom →L[ℂ] ℂ := by
    let L := bareLinear hA hD k
    refine ⟨L, continuous_of_continuousAt_zero (bareLinear hA hD k) ?_⟩
    change ContinuousAt _ _
    unfold ContinuousAt
    rw [map_zero]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (.of_forall fun _=> norm_nonneg _) (.of_forall (bounded_bare hA hD k)) ?_ )
    suffices G : wavePrice (0 : Probe Mom) (N+2) * bareCost N A D = 0 by exact G ▸ ((wavePrice_cont (N+2)|>.continuousAt.tendsto).mul_const _)
    unfold wavePrice orderCost Probe.size; simp [map_zero]
noncomputable def cauchyCLM (k : Fin 2) : Probe Mom→L[ℂ] ℂ := (bareCLM hA hD k).comp Probe.hat
lemma cauchy_eval (k f) : cauchyCLM hA hD k f=∫ x:Mom, Probe.hat f x * bare A D k x := rfl
lemma cauchy_eq (k f) : cauchyCLM hA hD k f=∫ x, Probe.hat f x * invariantBody A D k x ∂ν := by rw [cauchy_eval]; exact (exchangeBody hA hD k _).symm
lemma cauchy_bound (k f) : ‖cauchyCLM hA hD k f‖ ≤ ((2:ℝ)^(N+2)*bareCost N A D)*orderCost (Probe.hat f) (N+2) := by
   unfold orderCost; rw [cauchy_eval]; refine (bounded_bare hA hD k (Probe.hat f)).trans_eq ?_; dsimp [orderCost,wavePrice]; ring
lemma cauchy_support (hx : Rule A D) (f) (hf : CC f) (hO : (0:Mom)∉tsupport f) (k) : cauchyCLM hA hD k f=0 := by
    have H := cauchy_raw hA hD hx f hf hO
    rw [cauchy_eq]
    fin_cases k; · simpa only [Fin.reduceFinMk,invariantBody,ite_true,if_pos (Eq.refl (0:Fin 2))] using H.1
    simpa only [Fin.reduceFinMk,invariantBody,ite_false,if_neg (by decide : (1:Fin 2) ≠0),real_smul] using H.2
end YM.Trace.Shell
