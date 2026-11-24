import YM.Trace.Fock.MassParts
noncomputable section
set_option autoImplicit false
namespace YM.Trace.Shell
open Filter Function Set MeasureTheory YM Boundary
open scoped Pointwise Topology BigOperators ENNReal InnerProductSpace
lemma pow_ratio {a b : ℕ} (h : a<b) :
    Tendsto (fun t:ℝ=>t^a/(t^b)) atTop (𝓝 0) := by
 have H := (tendsto_inv_atTop_zero (𝕜:=ℝ)).pow (b-a)
 have hne : b-a≠0 := by omega
 refine (Tendsto.congr' (f₁:=fun t:ℝ=> (t⁻¹)^(b-a)) (by filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht; rw [inv_pow,pow_sub₀ _ ht.ne' h.le,mul_inv,inv_inv,mul_comm,div_eq_mul_inv])) (by simpa [zero_pow hne] using! H)
variable {n : ℕ} (w : ℕ → cell n)
lemma poly_scaled (s : Finset ℕ) (d : ℕ) (h : ∀ a∈s, a<d) : Tendsto (fun t:ℝ=> (t^(n+d))⁻¹ • linePoly s n w t) atTop (𝓝 0) := by
 unfold linePoly
 simp_rw [Finset.smul_sum,smul_smul,inv_mul_eq_div]
 have H := (tendsto_finsetSum s (fun i hi=> (pow_ratio (show n+i < n+d by have := h i hi; omega)).smul_const (w i)))
 simpa only [Finset.sum_const_zero,zero_smul] using! H
lemma poly_leading (t : Finset ℕ) (d : ℕ) (h : ∀ a∈t, a<d):
    Tendsto (fun r:ℝ=> (r^(n+d))⁻¹ • linePoly (insert d t) n w r) atTop (𝓝 (w d)) := by
 refine Tendsto.congr' (f₁:=fun r:ℝ=> w d + (r^(n+d))⁻¹ • linePoly t n w r) ?_ (by simpa using! ((poly_scaled w t d h).const_add (w d)))
 filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
 unfold linePoly; rw [Finset.sum_insert (fun ht=>lt_irrefl d (h d ht))]; -- proof
 rw [smul_add,smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_smul]
lemma scaled_suppressed (s : Finset ℕ) (d : ℕ) (hd : 4≤n+d)
    (h : Tendsto (fun t:ℝ=> (t⁻¹)^4 * ‖linePoly s n w t‖) atTop (𝓝 0)) : Tendsto (fun t:ℝ=> (t^(n+d))⁻¹ • linePoly s n w t) atTop (𝓝 0) := by
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 refine squeeze_zero' (.of_forall (fun _=> norm_nonneg _)) ?_ h
 filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
 rw [norm_smul,Real.norm_of_nonneg,inv_pow]; exact mul_le_mul_of_nonneg_right (((inv_le_inv₀ (pow_pos (by linarith : 0<t) _) (pow_pos (by linarith : 0<t) _)).2 (pow_le_pow_right₀ ht.le hd))) (norm_nonneg _)
 exact inv_nonneg_of_nonneg (pow_pos (by linarith : 0<t) _ |>.le)
lemma eliminate_deg (s : Finset ℕ) : Tendsto (fun t:ℝ=> (t⁻¹)^4 * ‖linePoly s n w t‖) atTop (𝓝 0) → ∀ d ∈ s, 4 ≤ n+d → w d=0 := by
 induction s using Finset.induction_on_max with
 | empty => simp
 | insert d s h IH =>
     intro ht m hm hm'
     have hd : 4 ≤ n+d := hm'.trans (by have h1 : m≤d := (Finset.mem_insert.mp hm).elim Eq.le (fun hs=>(h m hs).le); omega)
     have hz := scaled_suppressed w (insert d s) d hd ht
     have hd0 : w d=0 := tendsto_nhds_unique (poly_leading w s d h) hz
     rcases Finset.mem_insert.mp hm with rfl|hm
     · exact hd0
     have hn (t) : linePoly (insert d s) n w t=linePoly s n w t := by unfold linePoly; rw [Finset.sum_insert (fun hs=>lt_irrefl _ (h d hs)),hd0,smul_zero,zero_add]
     simp_rw [hn] at ht; exact IH ht m hm hm'
def subquartic (f : Test4) (v : Test4 →L[ℂ] Sum n) := Tendsto (fun r:ℝ=> r⁻¹^4 * ‖v (normalized f r)‖) atTop (𝓝 0)
lemma char_deg (s : Finset ℕ) (hs : Tendsto (fun t:ℝ=> t⁻¹^4 * ‖linePoly s n w t‖) atTop (𝓝 0)) : ∃ C≥(0:ℝ), (n≥4 → ∀ t, linePoly s n w t=0) ∧ ∀ t≥1, ‖linePoly s n w t‖ ≤ C*t^3 :=
 by
 have hw := eliminate_deg w s hs
 let C := ∑ i ∈ s, ‖w i‖
 refine ⟨C, Finset.sum_nonneg (fun _ _=>norm_nonneg _), fun hi t=>Finset.sum_eq_zero (fun i (hi':i∈s)=>by rw [hw i hi' (show 4≤n+i by omega), smul_zero]), fun t ht=> ?_⟩
 unfold linePoly C; rw [Finset.sum_mul]; apply (norm_sum_le ..).trans (Finset.sum_le_sum (fun i hi=> ?_))
 rw [norm_smul,Real.norm_of_nonneg (by positivity)]
 by_cases h: n+i<4; · rw [mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) (norm_nonneg _)
 rw [hw i hi (le_of_not_gt h),norm_zero,mul_zero,zero_mul]
end YM.Trace.Shell
