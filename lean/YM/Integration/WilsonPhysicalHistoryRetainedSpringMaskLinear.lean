import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskInteraction

/-! Combine actual signed physical mask errors before taking the absolute
integral. The two original variables may be completely correlated. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRunAction
open MeasureTheory Filter
open scoped Classical Topology
variable {Ω : Type*} [MeasurableSpace Ω]

theorem add_mask (μ : Measure Ω) [IsFiniteMeasure μ] {f g : Ω→ℝ} {A B C L : ℝ}
    (a : Measurable f ∧ (∀U,‖f U‖≤A) ∧ (∫U,‖f U‖ ∂μ)≤C)
    (b : Measurable g ∧ (∀U,‖g U‖≤B) ∧ (∫U,‖g U‖ ∂μ)≤L) :
    Measurable (fun U=>f U+g U) ∧ (∀U,‖f U+g U‖≤A+B) ∧
      (∫U,‖f U+g U‖ ∂μ)≤C+L := by
  have fi : Integrable f μ:=Integrable.of_bound a.1.aestronglyMeasurable A (Eventually.of_forall a.2.1)
  have gi : Integrable g μ:=Integrable.of_bound b.1.aestronglyMeasurable B (Eventually.of_forall b.2.1)
  refine ⟨a.1.add b.1,fun U=>(norm_add_le ..).trans (add_le_add (a.2.1 U) (b.2.1 U)),?_⟩
  apply (integral_mono (fi.add gi).norm (fi.norm.add gi.norm) (fun U=>norm_add_le (f U) (g U))).trans
  change (∫U,‖f U‖+‖g U‖ ∂μ)≤_
  rw [integral_add fi.norm gi.norm]
  exact add_le_add a.2.2 b.2.2

theorem scale_mask (μ : Measure Ω) (r : ℝ) {f : Ω→ℝ} {A C : ℝ}
    (a : Measurable f ∧ (∀U,‖f U‖≤A) ∧ (∫U,‖f U‖ ∂μ)≤C) :
    Measurable (fun U=>r*f U) ∧ (∀U,‖r*f U‖≤|r| *A) ∧
      (∫U,‖r*f U‖ ∂μ)≤|r| *C := by
  refine ⟨measurable_const.mul a.1,?_,?_⟩
  · intro U
    rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (a.2.1 U) (abs_nonneg _)
  simp_rw [norm_mul,Real.norm_eq_abs r]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left a.2.2 (abs_nonneg r)

end YM.Integration.OriginalMarkedRunAction
