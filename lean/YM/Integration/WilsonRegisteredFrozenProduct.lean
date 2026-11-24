import YM.Integration.WilsonCoherentRetainedIntegral

/-! The signed error of replacing both centered marks in one conditional
sample. All error moments are measured in the original positive law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredFrozenProduct
open Filter MeasureTheory

theorem product {a b A B k l : ℝ} (ak:|a-A|≤k) (bl:|b-B|≤l) :
    |a*b-A*B|≤k*|b| +l*|a| +k*l := by
  have first:=mul_le_mul_of_nonneg_right ak (abs_nonneg b)
  have second:=mul_le_mul_of_nonneg_right bl (abs_nonneg a)
  have crossed:=mul_le_mul ak bl (abs_nonneg _) ((abs_nonneg (a-A)).trans ak)
  calc
    _ = |(a-A)*b+(b-B)*a+(-(a-A)*(b-B))| := by congr 1;ring
    _ ≤ |(a-A)*b| +|(b-B)*a| +|-(a-A)*(b-B)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by simpa only [abs_mul,abs_neg] using add_le_add (add_le_add first second) crossed

theorem comparison {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω} {w t H a b A B:Ω→ℝ} {δ k l:ℝ}
    (original:Integrable (fun x=>w x*H x*(a x*b x)) μ)
    (moments:Integrable (fun x=>w x*|H x| *(k*|b x| +l*|a x| +k*l)) μ)
    (filed:AEStronglyMeasurable (fun x=>t x*H x*(A x*B x)) μ)
    (paid:∀ᵐ x ∂μ,0≤w x ∧ 0≤t x ∧ t x≤2*w x ∧ |w x-t x|≤δ*w x ∧ |a x-A x|≤k ∧ |b x-B x|≤l) :
    |(∫x,w x*H x*(a x*b x) ∂μ)-(∫x,t x*H x*(A x*B x) ∂μ)|≤
      δ*(∫x,w x*|H x*(a x*b x)| ∂μ)+2*(∫x,w x*|H x| *(k*|b x| +l*|a x| +k*l) ∂μ) := by
  have hf:Integrable (fun x=>w x*|H x*(a x*b x)|) μ:=original.norm.congr (paid.mono fun x hx=>by
    simp only [Real.norm_eq_abs,mul_assoc,abs_mul,abs_of_nonneg hx.1])
  let bill (x:Ω):=δ*(w x*|H x*(a x*b x)|)+2*(w x*|H x| *(k*|b x| +l*|a x| +k*l))
  have cash:Integrable bill μ:=(hf.const_mul δ).add (moments.const_mul 2)
  have bound:∀ᵐ x ∂μ,‖w x*H x*(a x*b x)-t x*H x*(A x*B x)‖≤bill x:=by
    filter_upwards [paid] with x hx
    exact (WilsonCoherentRetainedIntegral.point hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1
      (product hx.2.2.2.2.1 hx.2.2.2.2.2)).trans_eq (by dsimp [bill];ring)
  have residual:=cash.mono' (original.aestronglyMeasurable.sub filed) bound
  have measured:Integrable (fun x=>t x*H x*(A x*B x)) μ :=
    (original.sub residual).congr (ae_of_all _ fun x=>by dsimp;ring)
  have sum:(∫x,bill x ∂μ)=δ*(∫x,w x*|H x*(a x*b x)| ∂μ)+
      2*(∫x,w x*|H x| *(k*|b x| +l*|a x| +k*l) ∂μ):=by
    rw [show (∫x,bill x ∂μ)=_ from integral_add (hf.const_mul δ) (moments.const_mul 2)]
    simp only [integral_const_mul]
  rw [←integral_sub original measured,←sum]
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le (f:=fun x=>w x*H x*(a x*b x)-t x*H x*(A x*B x)) cash bound)

end YM.Integration.WilsonRegisteredFrozenProduct
end
