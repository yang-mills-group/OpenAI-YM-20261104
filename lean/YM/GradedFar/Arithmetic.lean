import Mathlib.Analysis.SpecialFunctions.Log.Basic
/-! Pure numerical steps used in converting the estimates. -/
namespace YM.FVA2.GradedFar
noncomputable section
open Filter Real
open scoped Topology

lemma from_exp (h : ℕ) (s : ℝ) :
    exp (-((h:ℝ)+1)*s) = (exp s)⁻¹^(h+1) := by
  rw [← exp_neg, ← exp_nat_mul, mul_neg]; push_cast; rw [neg_mul]

lemma collect (D B s g : ℝ) (a b h p : ℕ) (hs : 0 ≤ s) (hg : 0 ≤ g) (hD : 0 < D) (hB : 0 < B) :
    D * ((1+s)^a*exp (-((h:ℝ)+1)*s)) + (2*g)^(p+1) * (B*((1+s)^b*exp (-0*s))) ≤
      (D+2^(p+1)*B) * ((exp s)⁻¹^(h+1) + g^(p+1)) * (1+s)^(a+b) := by
  simp only [from_exp, neg_zero, zero_mul, exp_zero, mul_one, mul_pow]
  apply le_trans (b := D*((1+s)^(a+b) * (exp s)⁻¹^(h+1)) +
    (2^(p+1)*g^(p+1))*(B*(1+s)^(a+b)))
  · gcongr <;> (first | omega | linarith)
  rw [show (D+2^(p+1)*B) * ((exp s)⁻¹^(h+1) + g^(p+1)) * (1+s)^(a+b) =
    D*((1+s)^(a+b)*(exp s)⁻¹^(h+1)) + (2^(p+1)*g^(p+1))*(B*(1+s)^(a+b)) +
     ((1+s)^(a+b))*(D * g^(p+1)+2^(p+1)*B*((exp s)⁻¹^(h+1))) by ring]
  refine le_add_of_nonneg_right ?_; positivity
end
end YM.FVA2.GradedFar
