import YM.Trace.Fock.Slice
import Mathlib.Analysis.Calculus.ParametricIntegral
/-!
Temporal Cauchy tests on one momentum leg (spatial reflection for equal time).
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Trace.Shell
open YM MeasureTheory Function Filter Complex Boundary Set
open scoped Topology BigOperators ENNReal ContDiff Pointwise InnerProductSpace

lemma rho_reflect (p : Mom) : scalarWeight (-p)=scalarWeight p := by simp [scalarWeight]
lemma shell_reflect (f : Mom→ℝ) : (∫ p, f (-p)∂ν) = ∫ p, f p∂ν := by
  rw [integrate,integrate]
  simpa only [rho_reflect] using integral_neg_eq_self (f:=fun p => scalarWeight p * f p) volume -- rho_reflect loops
lemma shell_reflect_enn (s : Set Mom) (hs : MeasurableSet s) : ν (-s) = ν s := by
  unfold ν
  rw [show (-s) = (fun x:Mom => -x) ⁻¹' s from rfl, withDensity_apply _ (measurable_neg hs), withDensity_apply _ hs, ← lintegral_indicator (f:=_) (measurable_neg hs), ← lintegral_indicator (f:=_) hs]
  let G (p : Mom) := s.indicator (ENNReal.ofReal ∘ scalarWeight) p
  suffices H : (fun p => ((fun x:Mom => -x) ⁻¹' s).indicator (ENNReal.ofReal ∘ scalarWeight) p) = fun x => G (-x) by
       rw [H, MeasurePreserving.lintegral_comp_emb (Measure.measurePreserving_neg volume) (Homeomorph.neg Mom |>.measurableEmbedding) G]
  exact funext (fun p=>by by_cases h : -p∈s <;> exact (by simp_all [G,rho_reflect]))
instance reflection : Measure.IsNegInvariant ν := ⟨Measure.ext (fun s hs=> by rw [Measure.neg_apply]; exact shell_reflect_enn s hs)⟩
lemma shell_reflect_integrable {E : Type*} [NormedAddCommGroup E] {f : Mom→E} (hf : Integrable f ν) : Integrable (fun p => f (-p)) ν := by
     exact (Measure.measurePreserving_neg ..).integrable_comp_emb (Homeomorph.neg _).measurableEmbedding|>.2 hf
noncomputable def timePhase (p : Mom) (s : ℝ) := cexp (I * ↑(‖p‖) * ↑s)
lemma phase_norm (p : Mom) (s : ℝ) : ‖timePhase p s‖ = 1 := by simp [timePhase,norm_exp]
lemma phase_derivative (p : Mom) (t : ℝ) : HasDerivAt (timePhase p) (I*(‖p‖:ℂ)*timePhase p t) t :=
   (Complex.ofRealCLM.hasFDerivAt.hasDerivAt.const_mul (I * (‖p‖:ℂ))).cexp.congr_deriv (by simp [timePhase,mul_comm])

abbrev moment (s : ℕ) (p : Mom) := weight s p
structure Control (s:ℕ) (A : Mom→ℂ) : Prop where
   ae : AEStronglyMeasurable A ν
   integrable : Integrable (fun x=> ‖A x‖ / moment s x) ν
lemma Control.reflection {s A} (h : Control s A) : Control s (fun p=> A (-p)) where
   ae := h.ae.comp_quasiMeasurePreserving (Measure.measurePreserving_neg ..).quasiMeasurePreserving
   integrable := by simpa only [moment,weight,norm_neg] using shell_reflect_integrable h.integrable -- just apply after
lemma Control.phase_unchanged {s A} (h : Control s A) (t : ℝ) : Control s (fun p => timePhase p t * A p) :=
  { ae := AEStronglyMeasurable.mul (f:=fun p => timePhase p t) (by unfold timePhase; fun_prop) h.ae
    integrable := by simp_rw [norm_mul,phase_norm,one_mul]; exact h.integrable }
def wavePrice (f : Probe Mom) (s : ℕ) := orderCost f s * 2^s
lemma wavePrice_nonneg (f : Probe Mom) (s) : 0≤wavePrice f s := mul_nonneg (orderCost_nonneg ..) (by positivity)
lemma wavePrice_cont (s) : Continuous (fun f : Probe Mom=> wavePrice f s) := by exact (continuous_orderCost s).mul continuous_const
lemma window (f : Probe Mom) (s) (j) (p:Mom) (hs : j=s+2) : moment s p * (1+‖p‖)*‖f p‖ ≤ wavePrice f j := by
    subst j
    have hX : 1 ≤ 1+‖p‖ := by linarith [norm_nonneg p]
    have h := (wavePrice_nonneg f (s+2))
    have hM:= (mul_pos (weight_pos s p) (zero_lt_one.trans_le hX))
    apply le_trans (b:=moment s p*(1+‖p‖)*(wavePrice f (s+2)*(moment (s+2) p)⁻¹)) (mul_le_mul_of_nonneg_left (weighted_test f (s+2) p) hM.le)
    unfold moment weight
    suffices he : (1+‖p‖)^s*(1+‖p‖)*(wavePrice f (s+2)*((1+‖p‖)^(s+2))⁻¹) = wavePrice f (s+2)/(1+‖p‖) by rw [he]; exact div_le_self h hX
    field_simp; ring
lemma bounded_window (f : Probe Mom) (s : ℕ) (A : Mom→ℂ) : let B (p : Mom) := wavePrice f (s+2) * (‖A p‖ / moment s p)
    ∀ p, (1+‖p‖)*‖f p * A p‖ ≤ B p := by
     intro B p
     unfold B; rw [norm_mul]
     have h := weight_pos s p
     rw [mul_div_assoc'] -- wrong find
     apply (le_div_iff₀ h).2
     simpa [mul_assoc,mul_comm (weight ..),mul_left_comm] using! (mul_le_mul_of_nonneg_right (window f s _ p rfl) (norm_nonneg (A p)))
lemma Control.leg_regular {s A} (h : Control s A) (f : Probe Mom) : Integrable (fun x => f x * A x) ν ∧
    (∃ C, C=wavePrice f (s+2) * ∫ x, (‖A x‖ /moment s x)∂ν ∧ ‖∫ x, f x*A x∂ν‖ ≤ C) := by
   let M (x : Mom) := ‖A x‖ / moment s x
   have hl x : ‖f x * A x‖ ≤ wavePrice f (s+2) * M x := (le_mul_of_one_le_left (by positivity) (by linarith [norm_nonneg x] : (1:ℝ)≤1+‖x‖)).trans (bounded_window f s A x)
   have hm := h.integrable.const_mul (wavePrice f (s+2)); have hi := hm.mono' (f.continuous.aestronglyMeasurable.mul h.ae) (.of_forall hl)
   refine ⟨hi,_,rfl, (norm_integral_le_integral_norm ..).trans ?_⟩
   rw [← MeasureTheory.integral_const_mul]; exact integral_mono hi.norm hm hl
lemma slice_flow {s A} (h : Control s A) (f : Probe Mom) (t : ℝ) : let q (u : ℝ) (p : Mom) := timePhase p u * f p * A p
     HasDerivAt (fun r => ∫ p, q r p∂ν) (∫ p, I*(‖p‖:ℂ)*q t p∂ν) t := by
     intro q
     let R (u : ℝ) (p : Mom) := I * (‖p‖:ℂ) * q u p
     have hmic (r : ℝ) : Continuous (fun p : Mom=> timePhase p r) := by unfold timePhase; fun_prop
     have hm (r) : AEStronglyMeasurable (q r) ν := (hmic r |>.mul f.continuous |>.aestronglyMeasurable).mul h.ae
     have hme (r) : AEStronglyMeasurable (R r) ν := (Continuous.aestronglyMeasurable (Continuous.mul continuous_const (by fun_prop : Continuous (fun p:Mom => (‖p‖:ℂ))))|>.mul (hm r))
     have he : Integrable (q t) ν := by
       unfold q; have hQ := (h.phase_unchanged t).leg_regular f |>.1; simp_rw [← mul_assoc (f _)] at hQ; simpa only [mul_comm (f _) (timePhase ..)] using! hQ
     let D (x:Mom) := wavePrice f (s+2)*(‖A x‖/moment s x)
     have hD := h.integrable.const_mul (wavePrice f (s+2))
     apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ) (F:=fun r p=>timePhase p r * f p * A p) univ_mem (.of_forall hm) he (hme t) (ae_of_all _ fun p r hr => show ‖R r p‖ ≤ D p from ?_) hD
       (ae_of_all _ fun p r hr => ?_ )).2
     · unfold R q; simp only [norm_mul,norm_I,one_mul,norm_real,norm_norm,phase_norm,one_mul]
       rw [← mul_assoc]
       exact (mul_le_mul_of_nonneg_right (calc _ ≤ (1+‖p‖) * ‖f p‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)) (norm_nonneg _)).trans
          ((by rw [mul_assoc,← norm_mul]; exact bounded_window f s A p : (1+‖p‖) * ‖f p‖ * ‖A p‖ ≤ D p))
     · convert ((phase_derivative p r).mul_const _).mul_const _ using 1 <;> try rfl'
       dsimp only [R,q]; ring
end YM.Trace.Shell
