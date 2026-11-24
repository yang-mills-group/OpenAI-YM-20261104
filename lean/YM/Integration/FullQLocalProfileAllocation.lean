import YM.Integration.FullQLocalProfileSpecification

/-! Constructive positive widths for the finite pre-Run component diagram.
A decreasing scalar pays every finite-prefix strip and loss. Strict height
increase supplies one extra scalar factor on every edge. No Run, analytic
receipt, or width-payment premise is used. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.PreRun.Profile
open Lattice RG RG.Supply Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped BigOperators

variable {G : Gauge} {s : Sheet G} {q : MapPrices}
    {native : NativeComponentRecipe.Choice s}

/-- The internal part of an allocation; the external input remains free. -/
structure ComponentAllocation (D : Diagram s q native) where
  component : Fin D.count → ProfileWidths
  component_strip a i : (component a).width i < (D.strip a).width i
  same_mesh a b (hab : D.edge a b) i j (hij : j = i ∨ j = i + 1) :
    D.loss a b i * (component b).width j < (component a).width i

namespace ComponentAllocation

private def nodeCharge (D : Diagram s q native) (i : ℕ) (a : Fin D.count) : ℝ :=
  ((D.strip a).width i)⁻¹ + ∑ b : Fin D.count, D.loss a b i

private theorem nodeCharge_nonneg (D : Diagram s q native) (i : ℕ)
    (a : Fin D.count) : 0 ≤ nodeCharge D i a := by
  exact add_nonneg (inv_nonneg.mpr (((D.strip a).positive i).le))
    (Finset.sum_nonneg fun b _ => (D.loss_pos a b i).le)

private def charge (D : Diagram s q native) (upper : ProfileWidths) (i : ℕ) : ℝ :=
  (upper.width i)⁻¹ + ∑ a : Fin D.count, nodeCharge D i a

private theorem charge_nonneg (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) : 0 ≤ charge D upper i := by
  exact add_nonneg (inv_nonneg.mpr (upper.positive i).le)
    (Finset.sum_nonneg fun a _ => nodeCharge_nonneg D i a)

private theorem node_le_charge (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) (a : Fin D.count) : nodeCharge D i a ≤ charge D upper i := by
  calc
    _ ≤ ∑ b : Fin D.count, nodeCharge D i b :=
      Finset.single_le_sum (f := nodeCharge D i)
        (fun b _ => nodeCharge_nonneg D i b) (Finset.mem_univ a)
    _ ≤ _ := le_add_of_nonneg_left (inv_nonneg.mpr (upper.positive i).le)

private def budget (D : Diagram s q native) (upper : ProfileWidths) (i : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range (i + 1), charge D upper k

private theorem one_le_budget (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) : 1 ≤ budget D upper i := by
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun k _ => charge_nonneg D upper k)

private theorem budget_pos (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) : 0 < budget D upper i :=
  zero_lt_one.trans_le (one_le_budget D upper i)

private theorem charge_le_budget (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) : charge D upper i ≤ budget D upper i := by
  calc
    _ ≤ ∑ k ∈ Finset.range (i + 1), charge D upper k :=
      Finset.single_le_sum (f := charge D upper)
        (fun k _ => charge_nonneg D upper k)
        (Finset.mem_range.mpr (Nat.lt_succ_self i))
    _ ≤ _ := le_add_of_nonneg_left zero_le_one

private theorem budget_le_succ (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) : budget D upper i ≤ budget D upper (i + 1) := by
  have heq : budget D upper (i + 1) =
      budget D upper i + charge D upper (i + 1) := by
    unfold budget
    rw [Finset.sum_range_succ]
    ring
  rw [heq]
  exact le_add_of_nonneg_right (charge_nonneg D upper (i + 1))

private theorem upper_inv_le_budget (D : Diagram s q native)
    (upper : ProfileWidths) (i : ℕ) :
    (upper.width i)⁻¹ ≤ budget D upper i := by
  apply le_trans _ (charge_le_budget D upper i)
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun a _ => nodeCharge_nonneg D i a)

private theorem strip_inv_le_budget (D : Diagram s q native)
    (upper : ProfileWidths) (a : Fin D.count) (i : ℕ) :
    ((D.strip a).width i)⁻¹ ≤ budget D upper i := by
  apply le_trans _ ((node_le_charge D upper i a).trans (charge_le_budget D upper i))
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun b _ => (D.loss_pos a b i).le)

private theorem loss_le_budget (D : Diagram s q native) (upper : ProfileWidths)
    (a b : Fin D.count) (i : ℕ) : D.loss a b i ≤ budget D upper i := by
  calc
    _ ≤ ∑ c : Fin D.count, D.loss a c i :=
      Finset.single_le_sum (f := fun c => D.loss a c i)
        (fun c _ => (D.loss_pos a c i).le) (Finset.mem_univ b)
    _ ≤ nodeCharge D i a :=
      le_add_of_nonneg_left (inv_nonneg.mpr ((D.strip a).positive i).le)
    _ ≤ _ := (node_le_charge D upper i a).trans (charge_le_budget D upper i)

private def base (D : Diagram s q native) (upper : ProfileWidths) (i : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (budget D upper i)⁻¹

private theorem base_pos (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) : 0 < base D upper i :=
  mul_pos (by norm_num) (inv_pos.mpr (budget_pos D upper i))

private theorem budget_mul_base (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) : budget D upper i * base D upper i = (1 / 2 : ℝ) := by
  calc
    _ = (1 / 2 : ℝ) * (budget D upper i * (budget D upper i)⁻¹) := by
      unfold base
      ring
    _ = _ := by rw [mul_inv_cancel₀ (budget_pos D upper i).ne', mul_one]

private theorem mul_base_le_half (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) {x : ℝ} (hx : x ≤ budget D upper i) :
    x * base D upper i ≤ (1 / 2 : ℝ) := by
  exact (mul_le_mul_of_nonneg_right hx (base_pos D upper i).le).trans_eq
    (budget_mul_base D upper i)

private theorem base_le_one (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) : base D upper i ≤ 1 := by
  have h := mul_base_le_half D upper i (one_le_budget D upper i)
  rw [one_mul] at h
  exact h.trans (by norm_num)

private theorem base_succ_le (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) : base D upper (i + 1) ≤ base D upper i := by
  exact mul_le_mul_of_nonneg_left
    (inv_anti₀ (budget_pos D upper i) (budget_le_succ D upper i)) (by norm_num)

private theorem base_lt_of_inv_le (D : Diagram s q native) (upper : ProfileWidths)
    (i : ℕ) {x : ℝ} (hx : 0 < x) (hi : x⁻¹ ≤ budget D upper i) :
    base D upper i < x := by
  have h := mul_base_le_half D upper i hi
  calc
    _ = x * (x⁻¹ * base D upper i) := by
      rw [← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]
    _ ≤ x * (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left h hx.le
    _ < x := by linarith

private theorem power_le_base (D : Diagram s q native) (upper : ProfileWidths)
    (i k : ℕ) : base D upper i ^ (k + 1) ≤ base D upper i := by
  exact pow_le_of_le_one (base_pos D upper i).le (base_le_one D upper i)
    (Nat.succ_ne_zero k)

private theorem edge_bound (D : Diagram s q native) (upper : ProfileWidths)
    (a b : Fin D.count) (hab : D.edge a b) (i : ℕ) :
    D.loss a b i * base D upper i ^ (D.height b + 1) <
      base D upper i ^ (D.height a + 1) := by
  have hh : (D.height a + 1) + 1 ≤ D.height b + 1 :=
    Nat.add_le_add_right (Nat.succ_le_of_lt (D.edge_height hab)) 1
  have hp := pow_le_pow_of_le_one (base_pos D upper i).le
    (base_le_one D upper i) hh
  calc
    _ ≤ D.loss a b i * base D upper i ^ ((D.height a + 1) + 1) :=
      mul_le_mul_of_nonneg_left hp (D.loss_pos a b i).le
    _ = (D.loss a b i * base D upper i) *
        base D upper i ^ (D.height a + 1) := by
      rw [pow_succ]
      ring
    _ ≤ (1 / 2 : ℝ) * base D upper i ^ (D.height a + 1) :=
      mul_le_mul_of_nonneg_right
        (mul_base_le_half D upper i (loss_le_budget D upper a b i))
        (pow_nonneg (base_pos D upper i).le _)
    _ < _ := by
      have hpos := pow_pos (base_pos D upper i) (D.height a + 1)
      linarith

end ComponentAllocation

/-- Every fixed finite strict-height diagram has positive component widths.
The same construction satisfies strict same-index and one-step-lookahead
losses and lies below any prescribed positive output profile. -/
theorem components_below (D : Diagram s q native) (upper : ProfileWidths) :
    ∃ C : ComponentAllocation D,
      ∀ i, (C.component D.output).width i ≤ upper.width i := by
  let component : Fin D.count → ProfileWidths := fun a =>
    { width := fun i => ComponentAllocation.base D upper i ^ (D.height a + 1)
      positive := fun i => pow_pos (ComponentAllocation.base_pos D upper i) _ }
  have hstrip (a : Fin D.count) (i : ℕ) :
      (component a).width i < (D.strip a).width i :=
    (ComponentAllocation.power_le_base D upper i (D.height a)).trans_lt
      (ComponentAllocation.base_lt_of_inv_le D upper i ((D.strip a).positive i)
        (ComponentAllocation.strip_inv_le_budget D upper a i))
  have hedge (a b : Fin D.count) (hab : D.edge a b) (i j : ℕ)
      (hij : j = i ∨ j = i + 1) :
      D.loss a b i * (component b).width j < (component a).width i := by
    rcases hij with rfl | rfl
    · exact ComponentAllocation.edge_bound D upper a b hab _
    · have hp := pow_le_pow_left₀
        (ComponentAllocation.base_pos D upper (i + 1)).le
        (ComponentAllocation.base_succ_le D upper i) (D.height b + 1)
      exact (mul_le_mul_of_nonneg_left hp (D.loss_pos a b i).le).trans_lt
        (ComponentAllocation.edge_bound D upper a b hab i)
  refine ⟨{ component := component, component_strip := hstrip, same_mesh := hedge }, ?_⟩
  intro i
  exact (ComponentAllocation.power_le_base D upper i (D.height D.output)).trans
    (ComponentAllocation.base_lt_of_inv_le D upper i (upper.positive i)
      (ComponentAllocation.upper_inv_le_budget D upper i)).le

end YM.Integration.FullQLocal.PreRun.Profile
end
