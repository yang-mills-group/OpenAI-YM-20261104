import YM.Pert.Triangle.Orbit
/-!
Spherical transfer identities for the continuum expression. The epsilon-weighted
determinant at large radius is independent of the direction; the convolution
of the two gradient legs only supplies an off-site scalar.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
noncomputable section

namespace YM.Pert.Triangle
open Maxwell Analysis Set Function Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Matrix
local notation "I3" => Fin 3

-- Opposite helicity
lemma tensor_full (w:E4) {i j : I3} (hw : w≠0) :
    mixed i j w = (-8 * normal * (‖w‖^2)⁻¹^3) * atTensor i j w := by
  rw [mixed_contact _ _ hw]; unfold tensorSum; simp_rw [atHessian,second_Green hw,add_mul,Finset.sum_add_distrib]
  change -((∑ a:Axis, ∑ c:Axis,_ * rawProduct i j a c)+(∑ a:Axis, ∑ c:Axis,_ * rawProduct i j a c)) = _
  have he : (∑ a:Axis, ∑ c:Axis,-2*normal * (basis a) c * (‖w‖^2)⁻¹^2 * rawProduct i j a c) = 0 := by
    apply Eq.trans _ (diag_part (-2*normal * (‖w‖^2)⁻¹^2) i j)
    exact Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun c _=>by
      by_cases hx:a=c
      · rw [hx, basis_eq];simp
      have h' : c≠a := hx ∘ Eq.symm
      exact by simp only [basis_eq,if_neg hx,if_neg h',rawProduct,mul_zero,zero_mul]
  rw [he,zero_add]
  unfold atTensor; simp_rw [Finset.mul_sum,←Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun a _=> Finset.sum_congr rfl (fun v _=>by ring))

def wind (x : E4) : Matrix I3 I3 ℝ := fun i j=>atTensor i j x
def rawPolynomial (i j : I3) (x : Axis→ℝ) : ℝ := ∑ a,∑ b, x a * x b * ∑ c, (fanI true i a c:ℝ) * (fanI false j b c:ℝ)
lemma raw_match (x:E4) (i j :I3) : 2 * wind x i j = rawPolynomial i j (fun i=>x i) := by
  unfold wind atTensor rawPolynomial; simp only [Finset.mul_sum,product_rule,Int.cast_sum,Int.cast_mul, ←mul_assoc, show ∀a b:ℝ,2*a*b*2⁻¹=a*b by intro a b;ring]

end YM.Pert.Triangle
