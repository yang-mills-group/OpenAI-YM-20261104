import YM.Integration.WilsonCoherentSignedIntegral

/-! The changes to the signed source and to the positive driver have
separate costs measured in the original law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentRetainedIntegral
open Filter Set MeasureTheory

theorem point {w t H F P δ K:ℝ} (hw:0≤w) (ht:0≤t) (cap:t≤2*w) (change:|w-t| ≤δ*w)
    (source:|F-P| ≤K) :
    |w*H*F-t*H*P| ≤δ*(w*|H*F|)+(2*K)*(w*|H|) := by
  have a:|w-t| *|H*F| ≤δ*w*|H*F|:=mul_le_mul_of_nonneg_right change (abs_nonneg _)
  have b:|t*H| *|F-P| ≤(2*w)*|H| *K:=by
    rw [abs_mul,abs_of_nonneg ht]
    exact mul_le_mul (mul_le_mul_of_nonneg_right cap (abs_nonneg _)) source (abs_nonneg _) (by positivity)
  calc
    _ = |(w-t)*(H*F)+(t*H)*(F-P)| := by congr 1;ring
    _ ≤ |(w-t)*(H*F)| +|(t*H)*(F-P)| := abs_add_le _ _
    _ = |w-t| *|H*F| +|t*H| *|F-P| := by rw [abs_mul,abs_mul (t*H)]
    _ ≤ _ := (add_le_add a b).trans_eq (by ring)

theorem comparison {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω} {w t H F P:Ω→ℝ} {δ K:ℝ}
    (original:Integrable (fun x=>w x*H x*F x) μ) (absolute:Integrable (fun x=>w x*|H x|) μ)
    (filed:AEStronglyMeasurable (fun x=>t x*H x*P x) μ)
    (paid:∀ᵐ x ∂μ,0≤w x ∧ 0≤t x ∧ t x≤2*w x ∧ |w x-t x| ≤δ*w x ∧ |F x-P x| ≤K) :
    |(∫x,w x*H x*F x ∂μ)-(∫x,t x*H x*P x ∂μ)| ≤
      δ*(∫x,w x*|H x*F x| ∂μ)+(2*K)*(∫x,w x*|H x| ∂μ) := by
  have hf:Integrable (fun x=>w x*|H x*F x|) μ:=original.norm.congr (paid.mono fun x hx=>by
    simp only [Real.norm_eq_abs,mul_assoc,abs_mul,abs_of_nonneg hx.1])
  let bill (x:Ω):=δ*(w x*|H x*F x|)+(2*K)*(w x*|H x|)
  have cash:Integrable bill μ:=(hf.const_mul δ).add (absolute.const_mul _)
  have bound:∀ᵐ x ∂μ,‖w x*H x*F x-t x*H x*P x‖≤bill x:=by
    filter_upwards [paid] with x hx
    exact point hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2
  have residual:=cash.mono' (original.aestronglyMeasurable.sub filed) bound
  have trueFiled:Integrable (fun x=>t x*H x*P x) μ :=
    (original.sub residual).congr (ae_of_all _ fun x=>by dsimp;ring)
  have sum:(∫x,bill x ∂μ)=δ*(∫x,w x*|H x*F x| ∂μ)+(2*K)*(∫x,w x*|H x| ∂μ):=by
    rw [show (∫x,bill x ∂μ)=_ from integral_add (hf.const_mul δ) (absolute.const_mul (2*K))]
    simp only [integral_const_mul]
  rw [←integral_sub original trueFiled,←sum]
  simpa only [Real.norm_eq_abs] using (norm_integral_le_of_norm_le (f:=fun x=>w x*H x*F x-t x*H x*P x) cash bound)

end YM.Integration.WilsonCoherentRetainedIntegral
