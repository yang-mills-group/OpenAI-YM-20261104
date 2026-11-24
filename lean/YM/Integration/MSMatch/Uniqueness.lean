import YM.Comparison.RG02.Laplace.Trunc

/-!
The precise scale for the conditional prescription is ordinary integer powers of g
near 0+, after stripping specified leading factors. This includes *any* fixed external
Laurent prefactor `q(t) = t ^ l` with l an integer (positive on the punctured
side) and also the specified unmarked density leading factor, even when not expanded
by a power rule. Use the same q and accord remainder at `q(t)*t^(n+1)`, not at a
claimed regulator-uniform rate. No hypothesis on differentiability of q.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSMatch
open Comparison.RG02.Laplace Filter PertExtension.Series.Tested

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {q : ℝ → ℝ} {n : ℕ} {f : ℝ → E} {b c : ℕ → E}

def RelativeTrial (q : ℝ → ℝ) (b : ℕ → E) (f : ℝ → E) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in along, ‖f t - q t • peval b n t‖ ≤ q t * (C*t^(n+1))

lemma relativeTrial_iff (h : ∀ᶠ t in along, 0 < q t) :
    RelativeTrial q b f n ↔ Trial b (q⁻¹ • f) n := by
  have he (t : ℝ) (ht : 0 < q t) :
      ‖f t - q t • peval b n t‖ = q t * ‖((q⁻¹ • f) - peval b n) t‖ := by
    rw [← Real.norm_of_nonneg ht.le, ← norm_smul]
    rw [Pi.sub_apply, smul_sub, Real.norm_of_nonneg ht.le]
    change ‖f t - _‖ = ‖q t • ((q t)⁻¹ • f t) - q t • peval b n t‖
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  constructor
  · rintro ⟨C,hC,hv⟩
    refine ⟨C,hC,?_⟩
    filter_upwards [h,hv] with t ht hx
    rw [he t ht] at hx
    exact le_of_mul_le_mul_left hx ht
  rintro ⟨C,hC,hv⟩
  refine ⟨C,hC,?_⟩
  filter_upwards [h,hv] with t ht hx
  rw [he t ht]
  exact mul_le_mul_of_nonneg_left hx ht.le

theorem relativeTrial_unique (h : ∀ᶠ t in along, 0 < q t)
    (hq : RelativeTrial q b f n) (hv : RelativeTrial q c f n) :
    ∀ k ≤ n, b k = c k :=
  trial_gap ((relativeTrial_iff h).mp hq) ((relativeTrial_iff h).mp hv)

lemma laurent_unique (l : ℤ)
    (h : RelativeTrial (fun x => x^l) b f n) (hv : RelativeTrial (fun x => x^l) c f n) :
    ∀ k ≤ n, b k = c k := by
  apply relativeTrial_unique _ h hv
  filter_upwards [eventually_pos] with x hx
  exact zpow_pos hx _
end YM.Integration.MSMatch
