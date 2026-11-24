import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedBilateralTerm
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedBilateralDecay
open PostedBilateralWidth PostedBilateralBumpWages Filter Set
open scoped Topology ContDiff BigOperators Classical
variable {E : ℕ → Type*} [∀ d, NormedAddCommGroup (E d)] [∀ d, NormedSpace ℝ (E d)]
variable (a : ∀ d, ℕ → E d)

private theorem ratio {W : ℝ} (floor : 2 ≤ W) {n k : ℕ} (nk : k+1 ≤ n) :
    (W^n)⁻¹ * W^k * W ≤ (2:ℝ)^(k+1) * (1/2:ℝ)^n := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le nk
  have hw : W ≠ 0 := by linarith
  calc
    (W^(k+1+m))⁻¹ * W^k * W = (W^m)⁻¹ := by rw [pow_add,pow_succ]; field_simp
    _ ≤ ((2:ℝ)^m)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) floor m)
    _ = (2:ℝ)^(k+1) * (1/2:ℝ)^(k+1+m) := by rw [one_div,inv_pow,pow_add (2:ℝ) (k+1) m]; field_simp

theorem original (d k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, d ≤ n → k+1 ≤ n → ∀ t : ℝ,
    ‖iteratedDeriv k (fun y => PostedBilateralFieldCutoff.weight a n y • a d n) t‖ ≤
      C * ((n+1:ℝ)^k * (1/2:ℝ)^n) := by
  obtain ⟨B,hB,bound⟩ := PostedBilateralBumpWages.original k
  have hs : 0 ≤ size a d := by unfold size; positivity
  refine ⟨B * size a d * 2^(k+1),by positivity,?_⟩
  intro n dn nk t
  let W := width a n
  have hw : 2 ≤ W := PostedBilateralWidth.floor a n
  have hp : 0 ≤ W := by linarith
  have inc := PostedBilateralWidth.original a d n dn
  rw [PostedBilateralTerm.original]
  change (W^n)⁻¹ * W^k * ‖iteratedDeriv k (profile n) (W*t)‖ * ‖a d n‖ ≤ _
  calc
    _ ≤ (W^n)⁻¹ * W^k * (B * ((n+1:ℝ)^k*2^n)) * ‖a d n‖ := by
      gcongr; exact bound n (W*t)
    _ = (B * (n+1:ℝ)^k * (W^n)⁻¹ * W^k) * (‖a d n‖*2^n) := by ring
    _ ≤ (B * (n+1:ℝ)^k * (W^n)⁻¹ * W^k) * (size a d*W) :=
      mul_le_mul_of_nonneg_left inc (by positivity)
    _ = (B * size a d * (n+1:ℝ)^k) * ((W^n)⁻¹ * W^k * W) := by ring
    _ ≤ (B * size a d * (n+1:ℝ)^k) * ((2:ℝ)^(k+1) * (1/2:ℝ)^n) :=
      mul_le_mul_of_nonneg_left (ratio hw nk) (by positivity)
    _ = _ := by ring
end IssuedBridge.PostedBilateralDecay
