import YM.Trace.Fock.Time

/-! Time evolution gives the branch Cauchy data at products of separated tests. -/
noncomputable section
set_option maxHeartbeats 300000
set_option autoImplicit false
namespace YM.Trace.Shell
open Filter Set Complex MeasureTheory YM Boundary Function
open scoped InnerProductSpace Topology BigOperators ContDiff ENNReal
variable {N : ℕ}
variable {A D : Mom→ℂ} (h : Control N A) (h' : Control N D) (hx : Rule A D)
noncomputable def thermalWave (A : Mom→ℂ) (f : Probe Mom) (r : ℝ) := ∫ p, timePhase p r * f p * A p ∂ν
noncomputable def thermalD (A : Mom→ℂ) (f : Probe Mom) (r : ℝ) := ∫ p, I * (‖p‖:ℂ) * (timePhase p r * f p * A p) ∂ν
include h in
lemma continuous_thermalWave (f) : Continuous (thermalWave A f) := continuous_iff_continuousAt.mpr (fun x=> (slice_flow h f x).continuousAt)
include h h' hx in
private lemma thermal_mass (f : Probe Mom) (hf : CC f) (hO : (0:Mom)∉tsupport f) {ε : ℝ} (he : ∀ r∈tsupport f, ε < ‖r‖) {g : ℝ→ℂ} (hg : tsupport g ⊆ Ioo (-ε) ε) (hc : HasCompactSupport g) (ht : ContDiff ℝ ∞ g) :
    ∫ t, thermalWave A (Probe.hat f) (-t) * g t = ∫ t, thermalWave (fun r=>D (-r)) (Probe.hat f) t * g t := by
    trans (∫ r, ((Probe.hat f) r * ∫ t, timePhase r (-t) * g t)*A r∂ν)
    · simpa [thermalWave] using! factorize_phase true (Probe.hat f) g ht.continuous hc h |>.symm
    refine Eq.trans ?_ (by simpa [thermalWave] using! factorize_phase false (Probe.hat f) g ht.continuous hc (Control.reflection h'))
    simpa only [if_true] using probe_exchange f hx hf hO ht hc he hg

private lemma open_result {f : ℝ→ℂ} (h : Continuous f) {U : Set ℝ} (ho : IsOpen U) (hv : ∀ g : ℝ→ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
     tsupport g ⊆ U → (∫ x:ℝ,g x • f x)=0) : ∀ x∈U, f x=0 := by
     have hm := ae_iff.mp (IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ:=volume) ho (h.locallyIntegrable.locallyIntegrableOn _) hv)
     intro x hx
     by_contra ht
     exfalso; exact (IsOpen.measure_pos volume (ho.inter h.isOpen_support) (by exact ⟨x,hx,ht⟩ : (U ∩ support f).Nonempty)).ne' (by simp only [Classical.not_imp] at hm; convert hm using 2; rfl) -- ¬→ and intersection not defeq

set_option maxHeartbeats 1200000 in
private lemma real_sTest {ε : ℝ} {V W : ℝ→ℂ} (hV : Continuous V) (hW : Continuous W)
      (heq : ∀ g : ℝ→ℂ, ContDiff ℝ ∞ g→HasCompactSupport g→tsupport g ⊆ Ioo (-ε) ε → (∫ x, V x * g x)= ∫ x, W x * g x)
      (g : ℝ→ℝ) (hh : ContDiff ℝ ∞ g) (hg : HasCompactSupport g) (ht : tsupport g ⊆ Ioo (-ε) ε) : ∫ x, g x • (V-W) x=0 := by
     have hJ := heq (Complex.ofReal ∘ g) (Complex.ofRealCLM.contDiff.comp hh) (hg.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero _).trans ht)
     change ∫ x, g x • (V x-W x) = (0:ℂ)
     simp only [smul_sub,real_smul, show ∀ x, (g x:ℂ) * V x = V x * (g x:ℂ) from fun x=>mul_comm .., show ∀ x, (g x:ℂ) * W x = W x * (g x:ℂ) from fun x=>mul_comm ..] -- not loop unless V defeq g coe; local variables
     have hs : HasCompactSupport (ofReal ∘ g) := hg.comp_left Complex.ofReal_zero
     have hc (G : ℝ→ℂ) : Continuous G → Integrable (fun x=> G x * (g x:ℂ)) (volume:Measure ℝ) := fun h=> (h.mul (continuous_ofReal.comp hh.continuous)).integrable_of_hasCompactSupport ((hg.comp_left Complex.ofReal_zero|>.smul_left (f:=G)))
     rwa [MeasureTheory.integral_sub (hc _ hV) (hc _ hW),sub_eq_zero]

include h h' hx in
lemma near_zero_values (f : Probe Mom) (hf : CC f) (hO : (0:Mom)∉tsupport f):
     ∀ᶠ t in 𝓝 (0:ℝ), thermalWave A (Probe.hat f) (-t) = thermalWave (fun r=>D (-r)) (Probe.hat f) t := by
     obtain ⟨ε,ht,he⟩ := empty_time_neighborhood f hf hO
     let U := Ioo (-ε) ε
     let V (t : ℝ) := thermalWave A (Probe.hat f) (-t); let W := thermalWave (fun p=>D (-p)) (Probe.hat f)
     have hV : Continuous V := (continuous_thermalWave (h:=h) (Probe.hat f)).comp (continuous_neg)
     have hW : Continuous W := continuous_thermalWave (Control.reflection h') _
     suffices H : ∀ t∈U, (V-W) t=0 by exact Filter.Eventually.mono (Ioo_mem_nhds (by linarith) ht) (fun x (hx:x∈U)=> sub_eq_zero.mp (H x hx))
     exact open_result (hV.sub hW) isOpen_Ioo (fun g hh hg hT => real_sTest hV hW (fun u hc₁ hc₂ hU => thermal_mass h h' hx f hf hO he hU hc₂ hc₁) g hh hg hT)


include h h' in
lemma thermal_integrable (f : Probe Mom) : Integrable (fun x => I*(‖x‖:ℂ)*(f x * A x)) ν ∧
     Integrable (fun x=> I*(‖x‖:ℂ) * (f x * D (-x))) ν := by
     have he (B) (hB : Control N B) : Integrable (fun x=> I * (‖x‖:ℂ)*(f x*B x)) ν :=
        by
           have hc := hB.integrable.const_mul (wavePrice f (N+2))
           apply hc.mono' ((Continuous.aestronglyMeasurable (Continuous.mul (g:=fun p:Mom => (‖p‖:ℂ)) continuous_const (by fun_prop))).mul (f.continuous.aestronglyMeasurable.mul hB.ae))
           refine Filter.Eventually.of_forall (fun p=> ?_)
           change ‖I * (‖p‖:ℂ) * (f p * B p)‖ ≤ _
           rw [norm_mul,norm_mul,norm_I,norm_real,norm_norm, one_mul]; exact (mul_le_mul_of_nonneg_right (by linarith : ‖p‖≤1+‖p‖) (norm_nonneg _)).trans (bounded_window f N B p)
     exact ⟨he A h,he _ h'.reflection⟩
include h in
lemma wave_derivative (f : Probe Mom) (p) : HasDerivAt (thermalWave A f) (thermalD A f p) p := (slice_flow h ..)
lemma reverse_derivative {f : ℝ→ℂ} {z : ℂ} {x : ℝ} (hfd : HasDerivAt f z (-x)) : HasDerivAt (fun k=> f (-k)) (-z) x := by
    convert (hfd.hasFDerivAt.comp x (hasDerivAt_neg x).hasFDerivAt).hasDerivAt using 1 <;> try rfl'
    change -z=((1:ℝ) • (-1:ℝ)) • z; simp
  

include h h' hx in
lemma cauchy_raw (f : Probe Mom) (hf : CC f) (hO : (0:Mom)∉tsupport f) (f₀ := Probe.hat f) (_h : f₀=Probe.hat f := by rfl) :
    (∫ r, f₀ r * (A r - D (-r))∂ν) = 0 ∧ (∫ r, f₀ r * (↑‖r‖ * (A r + D (-r)))∂ν)=0 := by
    subst f₀
    let b := fun r=>D (-r); let f₀ := Probe.hat f
    let G := thermalWave A f₀; let S := thermalWave b f₀
    have hg: (fun r=>G (-r)) =ᶠ[𝓝 (0:ℝ)] S := near_zero_values h h' hx _ hf hO
    have ht := Filter.EventuallyEq.eq_of_nhds hg
    have hId : ∀ (q : Probe Mom) (v : Mom→ℂ), thermalWave v q 0 = ∫ p, q p * v p∂ν := by unfold thermalWave; simp [timePhase]
    have hE : ∀ v, Control N v → Integrable (fun x => (Probe.hat f) x * v x) ν := fun v h=> (h.leg_regular _).1
    constructor
    · simpa only [G,S,neg_zero ,Function.comp_apply, b, hId, mul_sub, MeasureTheory.integral_sub (hE _ h) (hE _ h'.reflection)] using sub_eq_zero.mpr ht
    have hD := reverse_derivative (x:=0) (f:=G) (z:=thermalD A f₀ (-0)) (by simpa using wave_derivative h f₀ 0)
    have heq := (hD.congr_of_eventuallyEq hg.symm).unique (wave_derivative (h'.reflection) f₀ 0)
    have hOr (v : Mom→ℂ) : thermalD v f₀ 0 = ∫ p,I*‖p‖*(f₀ p * v p) ∂ν := by unfold thermalD; simp [timePhase]
    have heQ : thermalD A f₀ 0 + thermalD b f₀ 0 = 0 := by rw [← heq,neg_zero,add_neg_cancel]
    refine mul_left_cancel₀ (a:=I) Complex.I_ne_zero (Eq.trans ?_ (heQ.trans (mul_zero _).symm))
    rw [hOr,hOr,← MeasureTheory.integral_add (thermal_integrable h h' ..|>.1) (thermal_integrable h h' ..|>.2),← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (.of_forall fun r => by ring)
end YM.Trace.Shell
