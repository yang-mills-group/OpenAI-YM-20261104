import YM.Integration.WilsonPhysicalHistoryRetainedSpringSite
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMean

/-! Absolute summation of signed mask errors at one occupied site under one measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open MeasureTheory Finset RG Wilson
open scoped Classical Topology BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem mask_sum_price (μ : Measure Ω) [IsFiniteMeasure μ] (f : ℕ→Ω→ℝ)
    {d : ℕ→ℝ} {C A B : ℝ} (bank : SumBudget d C) (ca : 0≤A) (cb : 0≤B)
    (mf : ∀ i,Measurable (f i)) (cap : ∀ i z,‖f i z‖≤d i*A)
    (each : ∀ i,(∫z,‖f i z‖ ∂μ)≤d i*B) :
    (∀z,Summable fun i=>‖f i z‖) ∧
    (∀z,‖∑'i,f i z‖≤C*A) ∧
    (∫z,‖∑'i,f i z‖ ∂μ)≤C*B := by
  have pay:=bank.2.1.mul_right A
  have summ (z) : Summable fun i=>‖f i z‖ :=
    Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>cap i z) pay
  have full (z) : ∑'i,‖f i z‖ ≤ C*A := by
    apply ((summ z).tsum_le_tsum (fun i=>cap i z) pay).trans
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right bank.2.2 ca
  have dom (z) := norm_tsum_le_tsum_norm (summ z)
  have bound (z) : ‖∑'i,f i z‖≤C*A := (dom z).trans (full z)
  have absInt : Integrable (fun z=>∑'i,‖f i z‖) μ :=
    Integrable.of_bound (Measurable.tsum fun i=>(mf i).norm).aestronglyMeasurable _
      (ae_of_all _ fun z=>by rw [Real.norm_of_nonneg (tsum_nonneg fun i=>norm_nonneg (f i z))];exact full z)
  have int : Integrable (fun z=>∑'i,f i z) μ :=
    Integrable.of_bound (Measurable.tsum mf).aestronglyMeasurable _ (ae_of_all _ bound)
  have receipts : Summable fun i=>∫z,‖f i z‖ ∂μ :=
    Summable.of_nonneg_of_le (fun _=>integral_nonneg fun _=>norm_nonneg _) each (bank.2.1.mul_right B)
  refine ⟨summ,bound,(integral_mono int.norm absInt dom).trans ?_⟩
  rw [←integral_tsum_of_summable_integral_norm (fun i=>(Integrable.of_bound (mf i).aestronglyMeasurable
    _ (ae_of_all _ (cap i))).norm) (by simpa only [Real.norm_eq_abs,abs_abs] using receipts)]
  apply (receipts.tsum_le_tsum each (bank.2.1.mul_right B)).trans
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right bank.2.2 cb

theorem mask_average_price (μ : Measure Ω) [IsFiniteMeasure μ] (f : Signed→Ω→ℝ)
    {A B : ℝ} (mf : ∀s,Measurable (f s)) (cap : ∀s z,‖f s z‖≤A)
    (each : ∀s,(∫z,‖f s z‖ ∂μ)≤B) :
    (∫z,‖Patch.average (fun s=>f s z)‖ ∂μ)≤B := by
  let c:=(Fintype.card Signed:ℝ)⁻¹
  have cp : 0<c := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  have fi (s) : Integrable (f s) μ := Integrable.of_bound (mf s).aestronglyMeasurable _ (ae_of_all _ (cap s))
  have orig : Integrable (fun z=>c*∑s,f s z) μ := (integrable_finsetSum _ fun s _=>fi s).const_mul _
  have sums : Integrable (fun z=>∑s,‖f s z‖) μ := integrable_finsetSum _ fun s _=>(fi s).norm
  have dom (z) : ‖c*∑s,f s z‖≤c*∑s,‖f s z‖ := by
    rw [norm_mul,Real.norm_of_nonneg cp.le]
    exact mul_le_mul_of_nonneg_left (norm_sum_le ..) cp.le
  change (∫ z,‖c*∑s,f s z‖ ∂μ)≤_
  apply (integral_mono orig.norm (sums.const_mul _) dom).trans
  rw [integral_const_mul,integral_finsetSum _ fun s _=>(fi s).norm]
  apply (mul_le_mul_of_nonneg_left (sum_le_sum (g:=fun _=>B) fun s _=>each s) cp.le).trans_eq
  rw [sum_const,card_univ,nsmul_eq_mul,←mul_assoc,show c*(Fintype.card Signed:ℝ)=1 from
    inv_mul_cancel₀ (Nat.cast_pos.mpr Fintype.card_pos).ne',one_mul]

end YM.Integration.OriginalMarkedRunAction
