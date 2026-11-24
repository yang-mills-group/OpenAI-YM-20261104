import YM.Integration.WilsonMaxwellThermometerRotations
import YM.Next.MAXWELL.Steps

/-! Actual continuum curvature slots under the eight proper rotations. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonMaxwellThermometerChiralSlots
open Set Function Maxwell Maxwell.Free XSpace.Chiral WilsonMaxwellThermometerRotations
open scoped BigOperators

def slot (s : Bool) (a : P) : Flavor 0 :=
  cell 0 (shard a) + sig s • cell (shard (a+1)) (shard (a+2))

theorem rotated_cell (o : Ortho) (a b : Axis) :
    actFlavor o 0 (cell a b) =
      ∑ i : Axis, ∑ j : Axis, (o.val i a * o.val j b) • cell i j := by
  apply LinearMap.ext
  intro f
  change turnJ o⁻¹ f.val a b (fun _ : Fin 0 => 0) = _
  rw [turns_apply]
  simp only [inv_entry, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (fun v => (o.val i a * o.val j b) * f.val i j v)
    (Subsingleton.elim _ _)

theorem pair_sum (C : Axis → Axis → ℝ) :
    ∑ i : Axis, ∑ j : Axis, C i j • cell i j =
      ∑ a : P, ((C 0 (shard a) - C (shard a) 0) • cell 0 (shard a) +
       (C (shard (a+1)) (shard (a+2)) - C (shard (a+2)) (shard (a+1))) •
        cell (shard (a+1)) (shard (a+2))) := by
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, cell_center, smul_zero]
  change _ = ((C 0 1-C 1 0) • cell 0 1 + (C 2 3-C 3 2) • cell 2 3) +
    ((C 0 2-C 2 0) • cell 0 2 + (C 3 1-C 1 3) • cell 3 1) +
    ((C 0 3-C 3 0) • cell 0 3 + (C 1 2-C 2 1) • cell 1 2)
  rw [cell_skew 1 0, cell_skew 2 0, cell_skew 3 0,
    cell_skew 3 2, cell_skew 1 3, cell_skew 2 1]
  module

private theorem rotate_raw (s t : Bool) (n : Ticket) (a : P) :
    (4 : ℝ) • actFlavor (rotation t n) 0 (slot s a) =
      ∑ i : Axis, ∑ j : Axis, (fieldCoefficient s t n a i j : ℝ) • cell i j := by
  let o := rotation t n
  rw [slot, map_add, map_smul, rotated_cell, rotated_cell, smul_add]
  simp only [Finset.smul_sum, smul_smul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← add_smul]
  congr 1
  simp only [coordinates, fieldCoefficient, Int.cast_add, Int.cast_mul, phase_cast]
  ring

theorem rotate (s t : Bool) (n : Ticket) (a : P) :
    (4 : ℝ) • actFlavor (rotation t n) 0 (slot s a) =
      ∑ b : P, (spin s t n a b : ℝ) • slot s b := by
  rw [rotate_raw, pair_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have he : (fieldCoefficient s t n a 0 (shard b) : ℝ) -
      (fieldCoefficient s t n a (shard b) 0 : ℝ) = (spin s t n a b : ℝ) := by
    exact_mod_cast WilsonMaxwellThermometerRotations.electric s t n a b
  have hm : (fieldCoefficient s t n a (shard (b+1)) (shard (b+2)) : ℝ) -
      (fieldCoefficient s t n a (shard (b+2)) (shard (b+1)) : ℝ) =
      (phase s : ℝ) * (spin s t n a b : ℝ) := by
    exact_mod_cast WilsonMaxwellThermometerRotations.magnetic s t n a b
  rw [he, hm, phase_cast, slot, smul_add, smul_smul, mul_comm]

theorem fixed (s t : Bool) (h : s ≠ t) (n : Ticket) (a : P) :
    actFlavor (rotation t n) 0 (slot s a) = slot s a := by
  have hh := rotate s t n a
  simp only [fixed_spin s t h, Int.cast_ite, Int.cast_ofNat, Int.cast_zero,
    ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hh
  exact (smul_right_injective _ (by norm_num : (4:ℝ) ≠ 0)) hh

theorem average (s : Bool) (a : P) : ∑ n : Ticket, actFlavor (rotation s n) 0 (slot s a) = 0 := by
  apply (smul_right_injective _ (by norm_num : (4:ℝ) ≠ 0))
  change (4 : ℝ) • (∑ n : Ticket, actFlavor (rotation s n) 0 (slot s a)) = (4 : ℝ) • (0 : Flavor 0)
  rw [Finset.smul_sum, smul_zero]
  simp_rw [rotate]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Int.cast_sum, moving_spin, Int.cast_zero, zero_smul, Finset.sum_const_zero]

end YM.Integration.WilsonMaxwellThermometerChiralSlots
