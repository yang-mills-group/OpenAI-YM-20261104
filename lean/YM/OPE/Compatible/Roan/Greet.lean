import YM.OPE.Compatible.Roan.Pond
/-! # Epoch exponent attenuation at clump separation. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Finset
variable {D R t s u A B Λ C L x ε:ℝ}
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Flock Lav Crown
noncomputable def Gov (s u:ℝ):= min s u/1024
lemma Gov_price (hs:0<s)(ht:0<u):0<Gov s u∧1024*Gov s u≤ s∧1024*Gov s u≤u:=by unfold Gov; rw [mul_div_cancel₀ _ (by norm_num)]; exact ⟨div_pos (lt_min hs ht) (by norm_num),min_le_left ..,min_le_right ..⟩
def Pulses (x D L t C u:ℝ):Prop:= ‖x‖≤ C∧ (D ≤ 16*t→ L ≤t→ ‖x‖≤ C*Real.exp (-(u/2*t)))∧ (16*t<D→ L≤D/32→‖x‖≤ C*Real.exp (-(u*(D/8)))) -- s unused
lemma Issue (ht:0 ≤t)(he:0≤D)(hp:R≤2*D)(hx:0≤ L)(hc:0<s)(hu:0<u)(hA:0≤A)(hB:‖B‖≤ A*Real.exp (-(s*L)))(h:Pulses x D L t C u):‖B*x‖≤ (A*C)*Real.exp (-Gov s u*(t+R+L)):=by
       obtain ⟨hV,hS,hU⟩:= Gov_price hc hu; let v:= Gov s u; have hC:0≤C:=(norm_nonneg x).trans h.1; rw [norm_mul]; apply le_trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _)); let B:= Real.exp (-(s*L)); have hT(p:ℝ)(hg:‖x‖≤ C*Real.exp (-p))(hq:v*(t+R+L) ≤ s*L+p): (A*B)*‖x‖ ≤ A*C*Real.exp (-v*(t+R+L)):= (mul_le_mul_of_nonneg_left hg (mul_nonneg hA (Real.exp_nonneg _))).trans (by rw [mul_mul_mul_comm, show B*_=Real.exp (-(s*L+p)) from (by unfold B; rw [← Real.exp_add];ring_nf)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (by rw [neg_mul];linarith only [hq])) (mul_nonneg hA hC))
       have hx':v*(t+R+L)≤ v*(t+2*D+L):=mul_le_mul_of_nonneg_left (by linarith only [hp]) hV.le; have hv(i j:ℝ)(hg:i ≤ j): v*i ≤ v*j:=mul_le_mul_of_nonneg_left hg hV.le; by_cases h':D≤16*t
       · by_cases hL:L≤t
         · apply hT (u/2*t) (h.2.1 h' hL); apply hx'.trans; apply (hv _ (34*t) (by linarith only [h',hL])).trans; nlinarith only [mul_le_mul_of_nonneg_right hU ht,mul_nonneg hV.le ht,mul_nonneg hc.le hx]
         apply hT 0 (by rw [neg_zero,Real.exp_zero,mul_one]; exact h.1); apply hx'.trans; apply (hv _ (34*L) (by linarith only [h',not_le.mp hL])).trans; nlinarith only [mul_le_mul_of_nonneg_right hS hx,mul_nonneg hV.le hx]
       by_cases hL:L≤D/32
       · apply hT (u*(D/8)) (h.2.2 (lt_of_not_ge h') hL); apply hx'.trans; apply (hv _ (3*D) (by linarith only [he,hL,not_le.mp h'])).trans; nlinarith only [mul_le_mul_of_nonneg_right hU he,mul_nonneg hV.le he, mul_nonneg hc.le hx]
       apply hT 0 (by rw [neg_zero,Real.exp_zero,mul_one]; exact h.1); apply hx'.trans; apply (hv _ (70*L) (by linarith only [he,hx,not_le.mp h', not_le.mp hL])).trans; nlinarith only [mul_le_mul_of_nonneg_right hS hx,mul_nonneg hV.le hx]
end YM.OPE.Borealis.Galea
