import YangMills.PhysicalOPE.PowerTrees
import YangMills.PhysicalOPE.FusionTree

set_option autoImplicit false
noncomputable section
namespace YangMills.WilsonProof

open Filter MeasureTheory Hierarchy
open scoped Classical

/-- When the test has nonzero mass somewhere, one point of its support supplies
the common scale inequalities required before the native integral estimate. -/
theorem onNonzeroTest {X : Type} [MeasurableSpace X] {μ : Measure X} {q : X → ℂ}
    {P : X → Prop} (nonzero : ¬ (q =ᵐ[μ] fun _ => 0))
    (onSupport : ∀ᵐ x ∂μ, q x ≠ 0 → P x) : ∃ x, q x ≠ 0 ∧ P x := by
  by_contra absent
  apply nonzero
  filter_upwards [onSupport] with x hx
  by_contra nz
  exact absent ⟨x, nz, hx nz⟩

/-- The two operands are independently integrable for an a.e. zero test,
including when the arrays outside its support do not satisfy the geometry. -/
theorem zeroTest {X : Type} [MeasurableSpace X] {μ : Measure X} {q : X → ℂ}
    (zero : q =ᵐ[μ] fun _ => 0) (first second : X → ℂ) (price gain : ℝ) :
    ‖∫ x, q x * first x ∂μ‖ ≤ (∫ x, ‖q x‖ ∂μ) * price ∧
      TestedDifference μ q first second (price * gain) := by
  have product (f : X → ℂ) : (fun x => q x * f x) =ᵐ[μ] fun _ => 0 := by
    filter_upwards [zero] with x hx
    simp [hx]
  have value (f : X → ℂ) : (∫ x, q x * f x ∂μ) = 0 := by
    rw [integral_congr_ae (product f), integral_zero]
  have mass : (∫ x, ‖q x‖ ∂μ) = 0 := by
    have he : (fun x => ‖q x‖) =ᵐ[μ] fun _ => (0 : ℝ) := by
      filter_upwards [zero] with x hx
      simp [hx]
    rw [integral_congr_ae he, integral_zero]
  refine ⟨by simp [value, mass], ⟨?_, ?_, by simp [value, mass]⟩⟩
  · exact (integrable_zero X ℂ μ).congr (product first).symm
  · exact (integrable_zero X ℂ μ).congr (product second).symm

namespace Tree
variable (t : FusionTree)

private def childRoot {v : t.Vertex} (p : t.Child v) : t.Node :=
  Sum.elim Sum.inl (fun j : Fin t.branches => Sum.inr j.succ) p.val

private theorem child_below {v : t.Vertex} (p : t.Child v) : t.below (childRoot t p) v := by
  obtain ⟨i | j, h⟩ := p
  · exact ⟨0, h⟩
  · exact ⟨1, by simpa [childRoot, Function.iterate_one] using h⟩

private theorem child_contains {v : t.Vertex} (p : t.Child v) :
    t.inChild p (childRoot t p) := by
  obtain ⟨i | j, h⟩ := p
  · rfl
  · exact ⟨0, rfl⟩

private theorem at_child {v : t.Vertex} (p : t.Child v)
    (x : Fin t.leaves → Spacetime) (z : t.Vertex → Spacetime) :
    t.location x z (childRoot t p) = t.positions x z p := by
  obtain ⟨i | j, h⟩ := p <;> rfl

/-- Full subtree clearance on the public test gives its immediate child shape
at the same radius, including the endpoint at unit child/parent ratio. -/
theorem immediate {r M η : ℝ} {s : t.Vertex → ℝ} {x : Fin t.leaves → Spacetime}
    {z : t.Vertex → Spacetime} (separated : t.separatedAt r M η s x z) :
    s 0 = r ∧ (∀ v, 0 < s v) ∧ (∀ i, t.ratio s i ≤ 1) ∧
      ∀ v, Within (s v) M η (t.positions (v := v) x z) (z v) := by
  obtain ⟨root, positive, scales, children⟩ := separated
  refine ⟨root, positive, fun i => (div_le_one (positive _)).2 (scales i), ?_⟩
  intro v
  constructor
  · intro p
    simpa only [at_child] using (children v).1 (childRoot t p) (child_below t p)
  · intro p q ne
    simpa only [at_child] using (children v).2 p q ne _ _ (child_contains t p) (child_contains t q)

end Tree
end YangMills.WilsonProof
