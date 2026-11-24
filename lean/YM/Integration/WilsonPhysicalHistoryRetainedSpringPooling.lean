import YM.Integration.WilsonPhysicalHistoryRetainedSpringVisits

/-! The path expenditure extends to zero-cost colours and to the original
countable list by monotone convergence at every requested moment order. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter MeasureTheory Finset
open scoped BigOperators Classical Topology ENNReal
variable {Ω ι : Type*} [MeasurableSpace Ω]

theorem pool_finite (μ : Measure Ω) (S : Finset ι) (c : ι→ℝ) (f : ι→Ω→ℝ)
    (cost : ∀ i∈S,0≤c i) (positive : ∀ i∈S,∀ z,0≤f i z)
    (meas : ∀ i∈S,AEStronglyMeasurable (f i) μ) (l : ℕ)
    (paid : ∀ i∈S,Integrable (fun z=>(f i z)^(l+1)) μ ∧
      (∫ z,(f i z)^(l+1) ∂μ)≤(c i)^(l+1)) :
    Integrable (fun z=>(∑ i∈S,f i z)^(l+1)) μ ∧ (∫ z,(∑ i∈S,f i z)^(l+1) ∂μ)≤(∑ i∈S,c i)^(l+1) := by
  let T:=∑ i∈S,c i
  have enlarged (e : ℝ) (he : 0<e) : Integrable (fun z=>(∑ i∈S,f i z)^(l+1)) μ ∧
      (∫ z,(∑ i∈S,f i z)^(l+1) ∂μ)≤(T+(S.card:ℝ)*e)^(l+1) := by
    have h:=QLocalMeasuredPathMoments.pooled μ S (fun i=>c i+e) f
      (fun i hi=>add_pos_of_nonneg_of_pos (cost i hi) he) positive meas l
      (fun i hi=>⟨(paid i hi).1,(paid i hi).2.trans (pow_le_pow_left₀ (cost i hi) (by linarith) _)⟩)
    simpa only [T,sum_add_distrib,sum_const,nsmul_eq_mul] using h
  refine ⟨(enlarged 1 zero_lt_one).1,?_⟩
  have lim : Tendsto (fun n : ℕ=>(T+(S.card:ℝ)*(1/((n:ℝ)+1)))^(l+1)) atTop (𝓝 (T^(l+1))) := by
    simpa only [mul_zero,add_zero] using (tendsto_const_nhds (x:=T) |>.add
      (tendsto_const_nhds (x:=(S.card:ℝ)) |>.mul tendsto_one_div_add_atTop_nhds_zero_nat)).pow (l+1)
  exact ge_of_tendsto' lim fun (n : ℕ)=>(enlarged (1/((n:ℝ)+1)) (one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one))).2

theorem pool_series (μ : Measure Ω) (c : ℕ→ℝ) (f : ℕ→Ω→ℝ) (hc : Summable c)
    (cost : ∀ i,0≤c i) (positive : ∀ i z,0≤f i z) (meas : ∀ i,Measurable (f i))
    (rows : ∀ z,Summable (fun i=>f i z)) (l : ℕ)
    (paid : ∀ i,Integrable (fun z=>(f i z)^(l+1)) μ ∧ (∫ z,(f i z)^(l+1) ∂μ)≤(c i)^(l+1)) :
    Integrable (fun z=>(∑' i,f i z)^(l+1)) μ ∧
      (∫ z,(∑' i,f i z)^(l+1) ∂μ)≤(∑' i,c i)^(l+1) := by
  let Y (n : ℕ) (z : Ω):=(∑ i∈range n,f i z)^(l+1)
  let A (z : Ω):=(∑' i,f i z)^(l+1)
  have y0 n z : 0≤Y n z:=pow_nonneg (Finset.sum_nonneg fun i _=>positive i z) _
  have a0 z : 0≤A z:=pow_nonneg (tsum_nonneg fun i=>positive i z) _
  have ym n : Measurable (Y n):=(Finset.measurable_sum _ (fun i _=>meas i)).pow_const _
  have am : Measurable A:=(Measurable.tsum fun i=>meas i).pow_const _
  have taxed n : Integrable (Y n) μ ∧ (∫ z,Y n z ∂μ)≤(∑' i,c i)^(l+1):=by
    have b:=pool_finite μ (range n) c f (fun i _=>cost i) (fun i _=>positive i)
      (fun i _=>(meas i).aestronglyMeasurable) l (fun i _=>paid i)
    exact ⟨b.1,b.2.trans (pow_le_pow_left₀ (Finset.sum_nonneg fun i _=>cost i)
      (hc.sum_le_tsum _ (fun i _=>cost i)) _)⟩
  have increasing : Monotone (fun n z=>ENNReal.ofReal (Y n z)):=by
    intro n m le z
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Finset.sum_nonneg fun i _=>positive i z)
      (Finset.sum_le_sum_of_subset_of_nonneg (range_mono le) (fun i _ _=>positive i z)) _)
  have eq (z : Ω) : ENNReal.ofReal (A z)=⨆ n,ENNReal.ofReal (Y n z) :=
    (iSup_eq_of_tendsto (fun n m le=>increasing le z)
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((rows z).hasSum.tendsto_sum_nat.pow (l+1)))).symm
  have bill : (∫⁻ z,ENNReal.ofReal (A z) ∂μ)≤ENNReal.ofReal ((∑' i,c i)^(l+1)):=by
    simp_rw [eq]
    rw [lintegral_iSup (μ:=μ) (f:=fun n z=>ENNReal.ofReal (Y n z)) (fun n=>ENNReal.measurable_ofReal.comp (ym n)) increasing]
    apply iSup_le
    intro n
    rw [←ofReal_integral_eq_lintegral_ofReal (taxed n).1 (ae_of_all _ (y0 n))]
    exact ENNReal.ofReal_le_ofReal (taxed n).2
  have ai : Integrable A μ:=⟨am.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal (ae_of_all _ a0)).2
    (bill.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨ai,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal ai (ae_of_all _ a0)] at bill
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg (tsum_nonneg cost) _)).mp bill

end YM.Integration.OriginalMarkedRunAction
