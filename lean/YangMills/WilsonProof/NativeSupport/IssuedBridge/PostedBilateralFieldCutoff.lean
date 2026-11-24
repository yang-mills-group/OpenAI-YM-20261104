import YM.Integration.WilsonPositionGradedCutoffs
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedBilateralFieldCutoff
open YM.Integration Function Filter Set Finset
open scoped Topology ContDiff Classical BigOperators
variable {E : ℕ→Type*} [∀ d,NormedAddCommGroup (E d)] [∀d,NormedSpace ℝ (E d)]
variable (a : ∀ d,ℕ→E d)

private def size (d : ℕ) : ℝ := 1+∑n∈range (d+1),‖a d n‖
private def scaled (d n : ℕ) : E d := (size a d)⁻¹ • a d n
private def cap (n : ℕ) : ℝ := 1+∑ d∈range (n+1),‖scaled a d n‖
private def width (n : ℕ) : ℝ := 2^(n+1)*(1+cap a n)+(n:ℝ)+1

def weight (n : ℕ) (t : ℝ) : ℝ :=
  Real.smoothTransition (2 + width a n*t) * WilsonPositionGradedCutoffs.weight a n t

theorem original (n : ℕ) : ContDiff ℝ ∞ (weight a n) ∧
    ∀ t : ℝ, 0 ≤ t → weight a n t = WilsonPositionGradedCutoffs.weight a n t := by
  have hw : 0 ≤ width a n := by unfold width cap; positivity
  constructor
  · change ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (2 + width a n*t) *
      (Real.smoothTransition (2 - width a n*t) * t^n))
    fun_prop
  · intro t ht
    have h : 1 ≤ 2 + width a n*t := by linarith [mul_nonneg hw ht]
    simp only [weight,Real.smoothTransition.one_of_one_le h,one_mul]
end IssuedBridge.PostedBilateralFieldCutoff
