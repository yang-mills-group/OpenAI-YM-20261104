import YM.Integration.WilsonPhysicalHistoryRetainedSpringPooling

/-! Pool the signed contributions of a finite list and the entering low path
in the single measure of the chamber. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open MeasureTheory Finset
open scoped BigOperators Classical

theorem roster_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {k M : ℕ} (limit : k≤M)
    (l : ℕ) {c : ℝ} (h : 0≤c) (r : Fin k→Ω→ℂ) (s : Ω→ℂ)
    (rows : ∀ i,Integrable (r i) μ ∧ Integrable (fun z=>‖r i z‖^(l+1)) μ ∧
      (∫ z,‖r i z‖^(l+1) ∂μ)≤c^(l+1))
    (extra : Integrable s μ ∧ Integrable (fun z=>‖s z‖^(l+1)) μ ∧ (∫ z,‖s z‖^(l+1) ∂μ)≤c^(l+1)) :
    let f:=fun z=>s z+∑ i,r i z
    Integrable f μ ∧ Integrable (fun z=>‖f z‖^(l+1)) μ ∧
      (∫ z,‖f z‖^(l+1) ∂μ)≤(((M:ℝ)+1)*c)^(l+1) := by
  intro f
  let a : Option (Fin k)→Ω→ℂ:=Option.elim' s r
  have paid : ∀ i,Integrable (a i) μ ∧ Integrable (fun z=>‖a i z‖^(l+1)) μ ∧
      (∫ z,‖a i z‖^(l+1) ∂μ)≤c^(l+1):=by
    rintro (_|i)
    · exact extra
    · exact rows i
  have eq : f=fun z=>∑ i,a i z:=by funext z; simp [f,a,Fintype.sum_option]
  have full : Integrable f μ :=by rw [eq]; exact integrable_finsetSum _ fun i _=>(paid i).1
  obtain ⟨whole,bill⟩:=pool_finite μ univ (fun _ : Option (Fin k)=>c) (fun i z=>‖a i z‖)
    (fun _ _=>h) (fun _ _ z=>norm_nonneg _) (fun i _=>(paid i).1.norm.aestronglyMeasurable)
    l (fun i _=>(paid i).2)
  have bynorm (z : Ω) : ‖f z‖^(l+1)≤(∑ i,‖a i z‖)^(l+1):=by
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [eq]
    exact norm_sum_le _ _
  have target:=whole.mono' ((continuous_pow (l+1)).comp_aestronglyMeasurable full.norm.aestronglyMeasurable)
    (ae_of_all _ fun z=>by rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact bynorm z)
  refine ⟨full,target,(integral_mono target whole bynorm).trans (bill.trans ?_)⟩
  apply pow_le_pow_left₀ (sum_nonneg (fun _ _=>h))
  simp only [sum_const,card_univ,Fintype.card_option,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  exact mul_le_mul_of_nonneg_right (add_le_add (Nat.cast_le.mpr limit) le_rfl) h

end YM.Integration.OriginalMarkedRunAction
