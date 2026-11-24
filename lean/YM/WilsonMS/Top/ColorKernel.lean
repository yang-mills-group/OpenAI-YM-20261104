import YM.WilsonMS.Top.GhostResponse

/-! # The based gauge parameter projection commutes with color

Check this concretely (even if choosing a matrix inverse elsewhere introduces
a mixing in coordinates). Needed when *changing* the ghost convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Quo
open Function Filter Set Finset Matrix Complex Lattice XSpace
open MS MS.Orbit MS.Bare MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Native Root Position Darboux
open MS.Orbit.Cog MS.Swirl
open scoped Topology ContDiff Matrix.Norms.Frobenius

variable {P : Period} (T : P.Tree) (G : Gauge)

section pos
variable (n : Side)

def colorBlock (n : Side) (p q : Site n) (i : Axis) : ℂ :=
  if q = -p then -(scaleZ n * midPhase (-Coord p) i * (Complex.I * ↑(wi n p i)) / muq n p) else 0

lemma angular_color (j k : G.ColorIndex) (p q : Site n) (i : Axis) :
    LK G n (j, p) ((i, k), q) = if j = k then colorBlock n p q i else 0 := by
  unfold colorBlock
  by_cases h : q = -p
  · subst q
    rw [if_pos rfl, L_matrix]
  rw [LF_off _ _ _ _ _ _ h]
  simp [h]

def locationBlock (n : Side) (p q : Site n) (i : Axis) : ℂ :=
  ∑ y : Site n, ∑ x : Site n, Bloch.cell p x * colorBlock n x y i * Bloch.cell q y

lemma geo (j k : G.ColorIndex) (p q : Site n) (i : Axis) :
    straightL G n (j, p) ((i, k), q) = if j = k then locationBlock n p q i else 0 := by
  let X := FFT.forward G.ColorIndex n
  let A := FFT.forward (Ax G) n
  let L := LK G n
  change (X * L * Aᵀ : Matrix (GaugeField G n) (SiteField G n) ℂ) _ _ = _
  have he (y : Ax G) (z : Site n) :
    (X * L : Matrix (GaugeField G n) (SiteField G n) ℂ) (j, p) (y, z) =
      ∑ x : Site n, Bloch.cell p x * L (j, x) (y, z) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single_of_mem j (mem_univ _)]
    · unfold X
      simp [FFT.forward]
    intro k _ hk
    simp [X, FFT.forward, Ne.symm hk]
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single_of_mem (i, k) (mem_univ _)]
  · simp_rw [he, transpose_apply,
      show ∀ y, A ((i, k), q) ((i, k), y) = Bloch.cell q y from fun _ => if_pos rfl, L, angular_color]
    by_cases h : j = k
    · simp_rw [if_pos h, Finset.sum_mul]
      rfl
    simp [h]
  intro z _ hz
  simp [A, FFT.forward, Ne.symm hz]

end pos

def rootedBlock (j : T.Nonroot) (i : P.Link) : ℂ :=
  locationBlock P.side (selected j.val) i.val.1 i.val.2 -
      locationBlock P.side (selected j.val) (P.reflect i.val).1 i.val.2 -
    (locationBlock P.side (selected T.root) i.val.1 i.val.2 -
      locationBlock P.side (selected T.root) (P.reflect i.val).1 i.val.2)

lemma tints (j : T.Nonroot) (i : P.Link) (x y : G.ColorIndex) :
    landL T G (j, x) (i, y) = if x = y then rootedBlock T j i else 0 := by
  let L := straightL G P.side
  let w (k : Site P.side) := (L * liftJ P G : Matrix _ _ ℂ) (x, k) (i, y)
  change w (selected j.val) - w (selected T.root) = _
  have hx k :
    w k =
      (if x = y then
        locationBlock P.side k i.val.1 i.val.2 - locationBlock P.side k (P.reflect i.val).1 i.val.2
      else 0) := by
    unfold w liftJ
    rw [Matrix.mul_sub, Matrix.sub_apply, Root.col_inclusion, Root.col_inclusion]
    change
      straightL G P.side _ ((i.val.2, y), i.val.1) -
          straightL G P.side _ ((i.val.2, y), (P.reflect i.val).1) =
        _
    rw [geo, geo]
    split <;>
      first
      | rfl
      | rw [sub_zero]
  rw [hx, hx]
  split <;>
    first
    | rfl
    | rw [sub_zero]

end YM.WilsonMS.Quo
