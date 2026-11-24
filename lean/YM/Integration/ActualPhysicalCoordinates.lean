import YM.Source.Construction
import YM.Extra.SOURCE_HISTORIES.Sizes

/-!
Exact terminal coordinates of the original physical fields.  The inverse
terminal map is retained in the coefficient cost.  This does not assert a
cutoff-independent bound on that map.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualPhysicalCoordinates
open Function Finset Lattice Wilson Source Labels Extra.Histories
open scoped BigOperators Classical

variable {G : Gauge} (C : Family G) (N p d : ℕ)

/-- Coordinates in the actual calibrated top basis, not the identity basis. -/
def coordinates (v : C.label d) : C.label d :=
  (C.factory d N p).terminal.symm v

def basis (i : (C.labels.level d).Index) : C.label d :=
  (C.factory d N p).terminal (Size.axis (C.labels.level d) i)

/-- The exact finite L1 cost of the original physical label in this basis. -/
def cost (v : C.label d) : ℝ :=
  (C.labels.level d).coeffSize (coordinates C N p d v)

theorem coordinates_terminal (v : C.label d) :
    coordinates C N p d ((C.factory d N p).terminal v) = v :=
  (C.factory d N p).terminal.symm_apply_apply v

theorem cost_terminal (v : C.label d) :
    cost C N p d ((C.factory d N p).terminal v) =
      (C.labels.level d).coeffSize v := by
  unfold cost
  rw [coordinates_terminal]

theorem reconstruct (v : C.label d) :
    (∑ i : (C.labels.level d).Index,
      coordinates C N p d v i • basis C N p d i) = v := by
  calc
    _ = (C.factory d N p).terminal
        (∑ i : (C.labels.level d).Index,
          coordinates C N p d v i • Size.axis (C.labels.level d) i) := by
      simp only [basis, map_sum, map_smul]
    _ = v := by
      rw [Size.sum_axes]
      exact (C.factory d N p).terminal.apply_symm_apply v

/-- Every original physical field is reconstructed at its original site. -/
theorem physical (v : C.label d) (o : Site (C.side N p)) :
    C.O N p v o = ∑ i : (C.labels.level d).Index,
      coordinates C N p d v i • C.O N p (basis C N p d i) o := by
  let L : C.label d →ₗ[ℂ] (Config G (C.side N p) → ℂ) :=
    (C.linearO N p d o).mk' (fun x : C.label d => C.O N p x o)
  have h := congrArg L (reconstruct C N p d v)
  simpa only [map_sum, map_smul, L, IsLinearMap.mk'_apply] using h.symm

theorem exact_mass (v : C.label d) :
    (∑ i : (C.labels.level d).Index, ‖coordinates C N p d v i‖) =
      cost C N p d v := rfl

theorem cost_nonneg (v : C.label d) : 0 ≤ cost C N p d v :=
  Work.G08.size_nonneg _ _

theorem cost_smul (z : ℂ) (v : C.label d) :
    cost C N p d (z • v) = ‖z‖ * cost C N p d v := by
  unfold cost coordinates
  rw [map_smul, Size.smul]

section FiniteWeights
variable {I : Type} [Fintype I]

theorem weighted_coordinates (w : I → ℂ) (v : I → C.label d) :
    coordinates C N p d (∑ i : I, w i • v i) =
      ∑ i : I, w i • coordinates C N p d (v i) := by
  simp only [coordinates, map_sum, map_smul]

/-- Independent finite weights remain inside the original coordinate cost. -/
theorem weighted_cost (w : I → ℂ) (v : I → C.label d) :
    cost C N p d (∑ i : I, w i • v i) ≤
      ∑ i : I, ‖w i‖ * cost C N p d (v i) := by
  unfold cost
  rw [weighted_coordinates]
  calc
    _ ≤ ∑ i : I, (C.labels.level d).coeffSize
        (w i • coordinates C N p d (v i)) :=
      Size.finite (C.labels.level d) Finset.univ _
    _ = _ := by simp only [Size.smul]

end FiniteWeights
end YM.Integration.ActualPhysicalCoordinates
