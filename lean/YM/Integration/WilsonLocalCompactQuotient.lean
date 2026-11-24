import YM.Integration.WilsonLocalReportingDensityIntegral

/-! Normalize a positive density with a two-sided relative error. Subtract the
original conditional mean before paying the signed numerator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactQuotient
open MeasureTheory Filter
open scoped Classical

private theorem multiply {x y δ:ℝ} (z:ℝ) (xn:0≤x) (bound:|x-y|≤δ*x) :
    ‖x*z-y*z‖≤δ*‖x*z‖:=by
  rw [←sub_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg xn,←mul_assoc]
  exact mul_le_mul_of_nonneg_right bound (abs_nonneg _)

private theorem shift {X:Type} [MeasurableSpace X] (μ:Measure X) {f h:X→ℝ}
    (fi:Integrable f μ) (hi:Integrable (fun x=>f x*h x) μ) (b:ℝ) :
    Integrable (fun x=>f x*(h x-b)) μ ∧
    (∫x,f x*(h x-b) ∂μ)=(∫x,f x*h x ∂μ)-b*∫x,f x ∂μ := by
  have eq:(fun x=>f x*(h x-b))=(fun x=>f x*h x-b*f x):=funext fun x=>by ring
  rw [eq]
  exact ⟨hi.sub (fi.const_mul b),by rw [integral_sub hi (fi.const_mul b),integral_const_mul]⟩

theorem centered {X:Type} [MeasurableSpace X] (μ:Measure X) {f p h:X→ℝ} {δ:ℝ}
    (dn:0≤δ) (fi:Integrable f μ) (one:(∫x,f x ∂μ)=1) (mp:Measurable p) (mh:Measurable h)
    (fhi:Integrable (fun x=>f x*h x) μ) (rates:∀x,0≤f x ∧ |f x-p x|≤δ*f x ∧ |f x-p x|≤δ*p x) :
    let B:=∫x,f x*h x ∂μ
    let Z:=∫x,p x ∂μ
    Integrable p μ ∧ Integrable (fun x=>p x*h x) μ ∧ 0<Z ∧ 1≤(1+δ)*Z ∧
    |(∫x,p x*h x ∂μ)/Z-B|≤δ*(1+δ)*∫x,‖f x*(h x-B)‖ ∂μ := by
  intro B Z
  have pi:Integrable p μ:=(WilsonLocalReportingDensityIntegral.difference μ fi mp
    (ae_of_all _ fun x=>by simpa only [Real.norm_eq_abs,abs_of_nonneg (rates x).1] using (rates x).2.1)).1
  have ph:Integrable (fun x=>p x*h x) μ:=(WilsonLocalReportingDensityIntegral.difference μ fhi (mp.mul mh)
    (ae_of_all _ fun x=>multiply (h x) (rates x).1 (rates x).2.1)).1
  have point (x):f x≤(1+δ)*p x:=by
    have left: f x-p x≤δ*p x:=(le_abs_self _).trans (rates x).2.2
    linarith
  have total:1≤(1+δ)*Z:=by
    calc 1 = ∫x,f x ∂μ := one.symm
         _ ≤ ∫x,(1+δ)*p x ∂μ := integral_mono fi (pi.const_mul _) point
         _ = (1+δ)*Z := integral_const_mul ..
  have zp:0<Z:=pos_of_mul_pos_right (zero_lt_one.trans_le total) (by linarith only [dn]:0≤1+δ)
  obtain ⟨centeredTrue,scalar⟩:=shift μ fi fhi B
  have zero:(∫x,f x*(h x-B) ∂μ)=0:=by rw [scalar,one,mul_one];exact sub_self B
  have bound:=(WilsonLocalReportingDensityIntegral.difference μ centeredTrue (mp.mul (mh.sub measurable_const))
    (ae_of_all _ fun x=>multiply (h x-B) (rates x).1 (rates x).2.1)).2
  change |(∫x,f x*(h x-B) ∂μ)-(∫x,p x*(h x-B) ∂μ)|≤δ*∫x,‖f x*(h x-B)‖ ∂μ at bound
  rw [zero,zero_sub,abs_neg,(shift μ pi ph B).2] at bound
  let W:=∫x,‖f x*(h x-B)‖ ∂μ
  have wn:0≤W:=integral_nonneg fun _=>norm_nonneg _
  have note:(∫x,p x*h x ∂μ)/Z-B=((∫x,p x*h x ∂μ)-B*Z)/Z:=by field_simp
  refine ⟨pi,ph,zp,total,?_⟩
  rw [note,abs_div,abs_of_pos zp,div_le_iff₀ zp]
  calc |(∫x,p x*h x ∂μ)-B*Z| ≤ δ*W := bound
       _ ≤ (δ*W)*((1+δ)*Z) := le_mul_of_one_le_right (mul_nonneg dn wn) total
       _ = δ*(1+δ)*W*Z := by ring

end YM.Integration.WilsonLocalCompactQuotient
