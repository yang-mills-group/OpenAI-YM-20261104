import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRestoredAnnularHearing

/-! A universal SIGNED exterior bill already bounds the jointly measured
absolute regular defect, without a separate a priori second moment for that
defect. Keep the complete true measure and arbitrary correlated L² exterior. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open MeasureTheory Set
open scoped Classical
variable {T:Type*}[MeasurableSpace T](μ:Measure T)

theorem tested_absolute (D:T→ℂ)(dm:Measurable D)(ε:ℝ)(ep:0≤ε)
    (dual:∀Z:T→ℂ,MemLp Z 2 μ → Integrable (fun t=>Z t*D t) μ ∧
      ‖∫t,Z t*D t ∂μ‖≤Real.sqrt (∫t,‖Z t‖^2 ∂μ)*ε)(Y:T→ℂ)(y2:MemLp Y 2 μ):
    Integrable (fun t=>‖Y t‖*‖D t‖) μ ∧
      (∫t,‖Y t‖*‖D t‖ ∂μ)≤Real.sqrt (∫t,‖Y t‖^2 ∂μ)*ε:=by
  let phase:=fun t=>(‖D t‖:ℂ)/D t
  let Z:=fun t=>(‖Y t‖:ℂ)*phase t
  have phaseM:Measurable phase:=(Complex.continuous_ofReal.measurable.comp dm.norm).div dm
  have zm:AEStronglyMeasurable Z μ:=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable y2.1.norm).mul phaseM.aestronglyMeasurable
  have unit (t:T):‖phase t‖≤1:=by
    by_cases empty:D t=0
    · simp [phase,empty]
    rw [show ‖phase t‖=‖D t‖/‖D t‖ by simp only [phase,norm_div,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)],
      div_self (norm_ne_zero_iff.mpr empty)]
  have zle (t:T):‖Z t‖≤‖Y t‖:=by
    dsimp only [Z]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
    exact mul_le_of_le_one_right (norm_nonneg _) (unit t)
  have z2:=y2.mono zm (.of_forall zle)
  obtain ⟨billed,ticket⟩:=dual Z z2
  have id:(fun t=>Z t*D t)=(fun t=>((‖Y t‖*‖D t‖:ℝ):ℂ)):=by
    funext t
    by_cases zero:D t=0
    · simp [Z,phase,zero]
    dsimp only [Z,phase]
    rw [mul_assoc,div_mul_cancel₀ _ zero,Complex.ofReal_mul]
  rw [id] at billed ticket
  have gross (t:T):0≤‖Y t‖*‖D t‖:=mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have ri:=billed.re
  change Integrable (fun t=>Complex.re ((‖Y t‖*‖D t‖:ℝ):ℂ)) μ at ri
  have bill:Integrable (fun t=>‖Y t‖*‖D t‖) μ:=by simpa only [Complex.ofReal_re] using ri
  rw [integral_complex_ofReal,Complex.norm_real,Real.norm_of_nonneg (integral_nonneg gross)] at ticket
  have zsq:Integrable (fun t=>‖Z t‖^2) μ:=(memLp_two_iff_integrable_sq_norm zm).1 z2
  have ysq:Integrable (fun t=>‖Y t‖^2) μ:=(memLp_two_iff_integrable_sq_norm y2.1).1 y2
  refine ⟨bill,ticket.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (integral_mono zsq ysq ?_)) ep)⟩
  exact fun t=>pow_le_pow_left₀ (norm_nonneg _) (zle t) 2

theorem crowd_spectator [IsFiniteMeasure μ] (F:Set T)(hm:MeasurableSet F)(Y:T→ℂ)(y2:MemLp Y 2 μ):
    Integrable (F.indicator (fun t=>‖Y t‖)) μ ∧
      (∫t,F.indicator (fun u=>‖Y u‖) t ∂μ)≤Real.sqrt (∫t,‖Y t‖^2 ∂μ)*Real.sqrt (μ.real F):=by
  let R:=F.indicator (fun t=>‖Y t‖)
  let Z:=fun t=>(R t:ℂ)
  have r0 (t:T):0≤R t:=by by_cases h:t∈F <;> simp [R,h]
  have rle (t:T):R t≤‖Y t‖:=by by_cases h:t∈F <;> simp [R,h]
  have zm:AEStronglyMeasurable Z μ:=Complex.continuous_ofReal.comp_aestronglyMeasurable (y2.1.norm.indicator hm)
  have same (t:T):‖Z t‖=R t:=by rw [show ‖Z t‖=‖(R t:ℝ)‖ from Complex.norm_real _,Real.norm_of_nonneg (r0 t)]
  have zle (t:T):‖Z t‖≤‖Y t‖:=(same t).le.trans (rle t)
  have z2:=y2.mono zm (.of_forall zle)
  obtain ⟨integralZ,fee⟩:=support_rms μ F hm Z z2 (fun t h=>by simp [Z,R,h])
  have ri:=integralZ.re
  change Integrable (fun t=>Complex.re (R t:ℂ)) μ at ri
  have realBill:Integrable R μ:=by simpa only [Complex.ofReal_re] using ri
  change ‖∫t,(R t:ℂ) ∂μ‖≤_ at fee
  rw [integral_complex_ofReal,Complex.norm_real,Real.norm_of_nonneg (integral_nonneg r0)] at fee
  have square:=integral_mono ((memLp_two_iff_integrable_sq_norm zm).1 z2)
    ((memLp_two_iff_integrable_sq_norm y2.1).1 y2) (fun t=>pow_le_pow_left₀ (norm_nonneg _) (zle t) 2)
  exact ⟨realBill,fee.trans (by rw [mul_comm];exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt square) (Real.sqrt_nonneg _))⟩

end YM.Integration.FVA1Physical.Exchange.RoseCut
