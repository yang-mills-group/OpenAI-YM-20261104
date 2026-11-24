import YM.UVExt.MetricLimit
/-! Order bounds and leading valuations on each factor to be multiplied before paying the sums. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Set Function Real
open scoped Classical BigOperators Topology InnerProductSpace ContDiff
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {P Q D D' A : ℝ} {f g h : ℝ→ℝ} {n k : ℕ}

structure Bill (P : ℝ) (n : ℕ) (f : ℝ→ℝ) : Prop where
  pos : 0 ≤ P
  smooth : ContDiffAt ℝ ω f 0
  pay k : ‖iteratedDeriv k f 0‖ ≤ P^k
  vanish k : k<n → iteratedDeriv k f 0=0

abbrev Tri (P D : ℝ) (f : ℝ→ℝ) := Bill P 1 f ∧ |iteratedDeriv 1 f 0| ≤ D
abbrev Quad (P D : ℝ) (f : ℝ→ℝ) := Bill P 2 f ∧ |iteratedDeriv 2 f 0| ≤ D^2

lemma Bill.multiply (hf : Bill P n f) (hg : Bill Q k g) : Bill (P+Q) (n+k) (f*g) := by
  have hF r := iteratedDeriv_mul (𝕜:=ℝ) (f:=f) (g:=g) (x:=0) (n:=r) (hf.smooth.of_le (by simp)) (hg.smooth.of_le (by simp))
  have hp := hf.pos; have hq := hg.pos
  refine ⟨by linarith, hf.smooth.mul hg.smooth, fun r=>?_ ,fun r hr=> ?_⟩
  · rw [hF,add_pow]
    refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i hi=>?_)
    simp only [norm_mul,Real.norm_natCast]
    have he := mul_le_mul_of_nonneg_left (hf.pay i) (Nat.cast_nonneg (α:=ℝ) (Nat.choose r i))
    exact (mul_le_mul he (hg.pay _) (norm_nonneg _) (by have := hf.pos; positivity)).trans_eq (by ring)
  rw [hF]
  exact Finset.sum_eq_zero fun i hi => if h:i<n then by rw [hf.vanish i h,mul_zero,zero_mul] else by rw [hg.vanish (r-i) (by simp only [Finset.mem_range] at hi; omega),mul_zero]

lemma top_two (h1 : Tri P D f) (h2 : Tri Q D' g) : Bill (P+Q) 2 (f*g) ∧ |iteratedDeriv 2 (f*g) 0| ≤ 2*D*D' := by
  have h1' := h1.1.vanish 0 zero_lt_one; have h2' := h2.1.vanish 0 zero_lt_one
  refine ⟨h1.1.multiply h2.1,?_
     ⟩
  rw [iteratedDeriv_mul (f:=f) (g:=g) (x:=0) (n:=2) (h1.1.smooth.of_le (by simp)) (h2.1.smooth.of_le (by simp))]; norm_num [show f 0=0 from h1', show g 0=0 from h2',Finset.sum_range_succ]
  simpa only [iteratedDeriv_one] using mul_le_mul (mul_le_mul_of_nonneg_left h1.2 (by norm_num)) h2.2 (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _ |>.trans h1.2))


lemma Bill.minus {g : ℝ→ℝ} (a : Bill P n f) (b : Bill P n g) (hn : 0<n) : Bill (2*P) n (f-g) := by
  have h r : iteratedDeriv r (f-g) 0 = _ := iteratedDeriv_sub (a.smooth.of_le (by simp)) (b.smooth.of_le (by simp))
  refine ⟨mul_nonneg (by norm_num) a.pos,a.smooth.sub b.smooth,fun k =>?_ ,fun k hk=>?_⟩
  · rw [h]
    by_cases hk : k=0
    · rw [hk, pow_zero]
      rw [a.vanish 0 (by omega),b.vanish 0 (by omega),sub_zero,norm_zero]; norm_num
    exact (norm_sub_le ..).trans ((add_le_add (a.pay _) (b.pay _)).trans (by rw [←two_mul,mul_pow]; exact mul_le_mul_of_nonneg_right (by have : (1:ℕ) ≤ k := Nat.one_le_iff_ne_zero.mpr hk; simpa only [pow_one] using (pow_le_pow_right₀ (show (1:ℝ)≤2 by norm_num) this)) (pow_nonneg a.pos _)))
  rw [h,a.vanish _ hk,b.vanish _ hk,sub_zero]

end YM.UVExt.Paths
