import YM.Integration.WilsonMaxwellThermometerJets

/-! Eight inverse-paired isoclinic rotations of the original Euclidean
four-space. The integer tables use twice the rotation matrix. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonMaxwellThermometerRotations
open Function Set Maxwell.Free XSpace.Chiral
open scoped BigOperators Matrix

abbrev Ticket := Fin 8

private def u : Ticket → ℤ := ![-1,-1,-1,-1,1,1,1,1]
private def v : Ticket → ℤ := ![-1,-1,1,1,-1,-1,1,1]
private def w : Ticket → ℤ := ![-1,1,-1,1,-1,1,-1,1]

/-- Left or right multiplication by the unit quaternion
`(1+u i+v j+w k)/2`, in the original ordered four axes. -/
def entry (side : Bool) (n : Ticket) : Matrix Axis Axis ℤ :=
  let h : ℤ := if side then 1 else -1
  !![1,-u n,-v n,-w n; u n,1,-h*w n,h*v n;
     v n,h*w n,1,-h*u n; w n,-h*v n,h*u n,1]

private theorem gram :
    ∀ t n a b, (∑ i : Axis, entry t n i a * entry t n i b) =
      (if a=b then 4 else 0) := by decide

private theorem transpose :
    ∀ t n a b, entry t n.rev a b = entry t n b a := by decide

def rotation (side : Bool) (n : Ticket) : Ortho := by
  let A : M4 := fun a b => (entry side n a b : ℝ) / 2
  refine ⟨A, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  have h := gram side n a b
  have hr : (∑ i : Axis, (entry side n i a : ℝ)*(entry side n i b : ℝ)) =
      (if a=b then 4 else 0) := by split_ifs at * <;> exact_mod_cast h
  simp only [A, div_mul_div_comm, ← Finset.sum_div, hr]
  split <;> norm_num

@[simp] theorem coordinates (t : Bool) (n : Ticket) (a b : Axis) :
    (rotation t n).val a b = (entry t n a b : ℝ)/2 := rfl

theorem reversed (t : Bool) (n : Ticket) : rotation t n.rev = (rotation t n)⁻¹ := by
  apply Subtype.ext
  ext a b
  rw [inv_entry, coordinates, coordinates, transpose]

private theorem mean_entry :
    ∀ t a b, (∑ n : Ticket, entry t n a b) = if a=b then 8 else 0 := by decide

theorem direction (t : Bool) (x : E4) :
    ∑ n : Ticket, Ortho.move (rotation t n) x = 4 • x := by
  ext a
  let L := EuclideanSpace.proj (𝕜:=ℝ) a
  change L (∑ n : Ticket, Ortho.move (rotation t n) x) = L (4 • x)
  rw [map_sum, map_nsmul]
  change (∑ n : Ticket, ∑ b : Axis, (entry t n a b : ℝ) / 2 * x b) = (4 : ℕ) • x a
  rw [Finset.sum_comm]
  have he (b : Axis) : (∑ n : Ticket, (entry t n a b : ℝ)) =
      (if a=b then 8 else 0) := by
    have h := mean_entry t a b; split_ifs at * <;> exact_mod_cast h
  simp_rw [← Finset.sum_mul, ← Finset.sum_div, he]
  simp [ite_div, ite_mul]
  left
  norm_num

/-- The doubled rotation on selfdual or anti-selfdual curvature slots.
The inverse on tensors gives the two transposed vector entries here. -/
def spin (s t : Bool) (n : Ticket) (a b : P) : ℤ :=
  ∑ i : Axis, ∑ j : Axis,
    entry t n i 0 * entry t n j (shard a) * triCoeff s b i j

def phase (s : Bool) : ℤ := if s then 1 else -1

theorem phase_cast (s : Bool) : (phase s : ℝ) = sig s := by
  cases s <;> rfl

def fieldCoefficient (s t : Bool) (n : Ticket) (a : P) (i j : Axis) : ℤ :=
  entry t n i 0 * entry t n j (shard a) +
    phase s * entry t n i (shard (a+1)) * entry t n j (shard (a+2))

private theorem form_table :
    ∀ s t n a b,
      let C := fieldCoefficient s t n a
      C 0 (shard b) - C (shard b) 0 = spin s t n a b ∧
      C (shard (b+1)) (shard (b+2)) - C (shard (b+2)) (shard (b+1)) =
        phase s * spin s t n a b := by decide

theorem electric (s t : Bool) (n : Ticket) (a b : P) :
    fieldCoefficient s t n a 0 (shard b) - fieldCoefficient s t n a (shard b) 0 =
      spin s t n a b := (form_table s t n a b).1

theorem magnetic (s t : Bool) (n : Ticket) (a b : P) :
    fieldCoefficient s t n a (shard (b+1)) (shard (b+2)) -
      fieldCoefficient s t n a (shard (b+2)) (shard (b+1)) =
      phase s * spin s t n a b := (form_table s t n a b).2

private theorem spin_table :
    ∀ (s t : Bool) (n : Ticket) (a b : P),
      s ≠ t → spin s t n a b = if a=b then 4 else 0 := by decide

theorem fixed_spin (s t : Bool) (h : s ≠ t) (n : Ticket) (a b : P) :
    spin s t n a b = if a=b then 4 else 0 := spin_table s t n a b h

private theorem active_table :
    ∀ (s : Bool) (a b : P), (∑ n : Ticket, spin s s n a b) = 0 := by decide

theorem moving_spin (s : Bool) (a b : P) : (∑ n : Ticket, spin s s n a b) = 0 :=
  active_table s a b

end YM.Integration.WilsonMaxwellThermometerRotations
