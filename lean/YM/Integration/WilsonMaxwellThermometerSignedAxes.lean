import YM.Integration.WilsonMaxwellThermometerChiralSlots

/-! A finite family of signed-coordinate rotations on the actual cap-four
source. Its two quaternionic sign averages and its spatial cycle project
to the two chiral scalar quadratics. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSignedAxes
open Maxwell Maxwell.Free XSpace.Chiral WilsonMaxwellThermometerRotations
open WilsonMaxwellThermometerChiralSlots
open scoped BigOperators

private def table : Axis → Axis → Axis :=
  ![![0,1,2,3],![1,0,3,2],![2,3,0,1],![3,2,1,0]]
private def negative : Axis → Axis → Bool :=
  ![![false,false,false,false],![false,true,false,true],![false,true,true,false],
    ![false,false,true,true]]
private theorem twice : ∀ i j : Axis, table i (table i j) = j := by decide
private def quat (s : Bool) (i : Axis) : Signed where
  perm := ⟨table i, table i, twice i, twice i⟩
  flip j := if s then negative i j else negative j i

private def shift (c : P) : Axis → Axis := Fin.cases 0 fun a => shard (a+c)
private theorem undo : ∀ (c : P) (a : Axis), shift (-c) (shift c a) = a := by decide
private def cycle (c : P) : Signed where
  perm := ⟨shift c, shift (-c), undo c, by intro a; simpa using undo (-c) a⟩
  flip _ := false

def frame (c : P) (u v : Axis) := cycle c * quat true u * quat false v

def character (h : Axis) (a : P) : ℤ := if h=0 ∨ h=shard a then 1 else -1
def weight (s : Bool) (u v : Axis) (a : P) := character (if s then u else v) a

private def number (r : Signed) (i j : Axis) : ℤ :=
  if r.perm j=i then (if r.flip j then -1 else 1) else 0
private def panel (r : Signed) (s : Bool) (a : P) (i j : Axis) : ℤ :=
  number r i 0 * number r j (shard a) +
  phase s * (number r i (shard (a+1)) * number r j (shard (a+2)))
private def cost (s : Bool) (c : P) (u v : Axis) (a b : P) : ℤ :=
  if a+c=b then weight s u v a else 0

private theorem signs : ∀ (s : Bool) (c : P) (u v : Axis) (a b : P),
    let C := panel (frame c u v) s a
    C 0 (shard b) - C (shard b) 0 = cost s c u v a b ∧
    C (shard (b+1)) (shard (b+2)) - C (shard (b+2)) (shard (b+1)) =
      phase s * cost s c u v a b := by decide

private theorem matrix_value (r : Signed) (i j : Axis) :
    (r.ortho.val i j) = (number r i j : ℝ) := by
  change r.matrix i j = _
  simp only [Signed.matrix_at, number]; split_ifs <;> norm_num

private theorem acted (r : Signed) (s : Bool) (a : P) :
    actFlavor r.ortho 0 (slot s a) =
      ∑ i : Axis, ∑ j : Axis, (panel r s a i j : ℝ) • cell i j := by
  rw [slot, map_add, map_smul, rotated_cell, rotated_cell]
  simp only [Finset.smul_sum, smul_smul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [← add_smul]
  simp only [panel, matrix_value, Int.cast_add, Int.cast_mul, phase_cast]

theorem turns (s : Bool) (c : P) (u v : Axis) (a : P) :
    actFlavor (frame c u v).ortho 0 (slot s a) = (weight s u v a : ℝ) • slot s (a+c) := by
  rw [acted, pair_sum]
  have val (b : P) : ((panel (frame c u v) s a 0 (shard b) : ℝ) -
      (panel (frame c u v) s a (shard b) 0 : ℝ)) • cell 0 (shard b) +
      ((panel (frame c u v) s a (shard (b+1)) (shard (b+2)) : ℝ) -
      (panel (frame c u v) s a (shard (b+2)) (shard (b+1)) : ℝ)) •
      cell (shard (b+1)) (shard (b+2)) = (cost s c u v a b : ℝ) • slot s b := by
    rw [← Int.cast_sub, ← Int.cast_sub, (signs s c u v a b).1, (signs s c u v a b).2]
    simp only [Int.cast_mul, phase_cast, slot, smul_add, smul_smul]
    rw [mul_comm (sig s)]
  simp_rw [val, cost, Int.cast_ite, Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem sign_pairs : ∀ (s t : Bool) (a b : P),
    (∑ u : Axis, ∑ v : Axis, weight s u v a * weight t u v b) =
      if s=t ∧ a=b then 16 else 0 := by decide

theorem square (s : Bool) (u v : Axis) (a : P) :
    (weight s u v a : ℝ) * (weight s u v a : ℝ) = 1 := by
  exact_mod_cast (show ∀ (s : Bool) (u v : Axis) (a : P),
    weight s u v a * weight s u v a = 1 from by decide) s u v a

end YM.Integration.WilsonMaxwellThermometerSignedAxes
