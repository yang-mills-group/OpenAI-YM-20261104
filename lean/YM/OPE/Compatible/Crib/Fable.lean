import YM.OPE.Compatible.Crib.Select
/-! # root Parse.Param smooth bills for real responses. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Crown
open Function Filter Set Finset
open scoped Topology BigOperators Classical ContDiff
open Silt Cloud Tensor PertExtension Flume Flume.Page Flume.Script Jargon Score Drift GaussianScore Series Libra Shell Char Spells Radial Stranded
variable {E:Type}{r s t D x C ε:ℝ}{p q k:ℕ}
variable [NormedAddCommGroup E][NormedSpace ℝ E]
section
variable {f:E→ℝ}{W Q:JetS E}
abbrev scope (W:JetS E)(t:ℝ):Prop:=∀ i:Phase, ‖W.seq i.val‖ ≤ t
abbrev fuel (W Q:JetS E)(b:ℝ):Prop:=∀ i:Phase, ‖W.seq i.val-Q.seq i.val‖≤ b
abbrev Jfare (t r:ℝ):=r + r*t + (r*t+r*t^2)
abbrev Jfair (t r:ℝ):= r + r*(t+1) + (r*(t+1)+ r*(t^2+2*t))
variable (hp:scope W t)(hW: ContDiff ℝ 3 f)(hR:∀ i:ℕ,i≤ 3 →∀ x:E,‖x‖≤ t →‖iteratedFDeriv ℝ i f x‖ ≤ r)
include hp hW hR
omit hW in private lemma γPay {x:E}(hx:‖x‖≤ t)(i:ℕ)(hi:i≤3): ‖γ f i W.s x‖ ≤ r*t^i:=by
         have hh:=hR i hi _ (hp 0); refine ((iteratedFDeriv ℝ i f W.s).le_opNorm ..).trans ?_; rw [prod_const, card_univ,Fintype.card_fin]; exact mul_le_mul hh (pow_le_pow_left₀ (norm_nonneg _) hx _) (pow_nonneg (norm_nonneg _) _) ((norm_nonneg _).trans hh)
lemma thickP (hq:0≤r) : scope (Jpiece W f) (Jfare t r):=by
       have hz:=γPay hp hR (x:=W.l) (hp 1) 0 (by omega); simp only [γ,iteratedFDeriv_zero_apply,pow_zero,mul_one] at hz; have hx:= γPay hp hR (x:=W.l) (hp 1) 1 (by omega); have he:=γPay hp hR (x:=W.h) (hp 2) 1 (by omega); have hv:=γPay hp hR (x:=W.l) (hp 1) 2 (by omega); simp only [γ,iteratedFDeriv_one_apply,pow_one] at hx he; have ht:0≤t:=(norm_nonneg _).trans (hp 0); have hb:0 ≤ r*t:= mul_nonneg hq ht; intro i; fin_cases i
       · apply hz.trans; unfold Jfare; linarith only[hq,hb,mul_nonneg hq (sq_nonneg t)]
       · apply hx.trans; unfold Jfare; linarith only[hq,hb,mul_nonneg hq (sq_nonneg t)]
       change ‖pointD _ _ _+1/2*pointD W.l (pointD W.l f) W.s‖ ≤ _; rw [lance (hW.of_le (by norm_num))]; apply (norm_add_le ..).trans; rw [norm_mul]; exact (add_le_add he ((mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans hv)).trans (le_add_of_nonneg_left (add_nonneg hq hb))
lemma Sun (h:scope Q t)(hq:fuel W Q ε)(hc:0≤r): fuel (Jpiece W f) (Jpiece Q f) (Jfair t r*ε):=by
       have hx:= Gaff f ε ε r (x:=W.s) (y:=Q.s) (v:=W.l) (w:=Q.l) (hp 0) (h 0) (hp 1) (h 1) (hq 0) (hq 1) hW hR; have he:=Gaff f ε ε r (x:=W.s) (y:=Q.s) (v:=W.h) (w:=Q.h) (hp 0) (h 0) (hp 2) (h 2) (hq 0) (hq 2) hW hR; have hz:=hx 2 (by norm_num); have hv:=hx 0 (by norm_num); specialize hx 1 (by norm_num); specialize he 1 (by norm_num); simp only [γ,iteratedFDeriv_zero_apply,pow_zero,mul_one,Nat.cast_zero,mul_zero,zero_mul,add_zero] at hv; simp only [γ,iteratedFDeriv_one_apply,pow_one,Nat.cast_one,mul_one,Nat.sub_self,pow_zero] at hx he
       have ht:0≤t:=(norm_nonneg _).trans (hp 0); have hb:0 ≤ r*(t^2+2*t):=by positivity
       have hs:0≤ ε := (norm_nonneg _).trans (hq 0); have hk:0≤ r*(t+1):=by positivity
       intro i; fin_cases i
       · apply hv.trans; apply mul_le_mul_of_nonneg_right _ hs; unfold Jfair; linarith only[hc,hk,hb] -- patch
       · apply hx.trans; rw [show r*ε*t+r*ε=r*(t+1)*ε from (by ring)]; apply mul_le_mul_of_nonneg_right _ hs; unfold Jfair;linarith only [hc,hk,hb]
       change ‖(pointD W.h _ _ + 1/2*pointD _ (pointD _ _ ) _)-(pointD _ _ _ + 1/2*pointD _ (pointD _ _) _)‖≤_; have h₀:ContDiff ℝ 2 f:= hW.of_le (by norm_num); rw [lance h₀,lance h₀, show pointD W.h f W.s+_-(pointD Q.h f Q.s+_)= (pointD W.h f W.s- pointD Q.h f Q.s)+1/2*(γ f 2 W.s W.l-γ f 2 Q.s Q.l) from (by ring)]
       apply (norm_add_le ..).trans; rw [norm_mul]; apply (add_le_add he ((mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans hz)).trans; rw [show r*ε*t+r*ε+(r*ε*t^2+r*(↑(2:ℕ):ℝ)*ε*t^(2-1:ℕ))= (r*(t+1)+r*(t^2+2*t))*ε from (by norm_num; ring)]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (add_nonneg hc hk)) hs
end
end YM.OPE.Crown
