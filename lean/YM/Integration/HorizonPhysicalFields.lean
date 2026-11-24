import YM.Integration.ActualPhysicalCoordinates
import YM.Extra.MULTISOURCE_TRAJECTORIES.Probes
import YM.RG02.Native.Supply

/-!
The original physical fields in one fixed section-polynomial alphabet.
The terminal inverse, engineering power, signed motion and conjugation
are retained in their actual coefficient vectors.  No bound uniform in
the cutoff or period is asserted for those vectors.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.HorizonPhysicalFields
open Function Finset Lattice Wilson RG Source Labels Marker
open Extra.Histories Extra.Trajectories RG02.Native
open scoped Classical BigOperators Topology

variable {G : Gauge} (C : Family G)

abbrev Slot {I : Type} (d : I → ℕ) := Σ i : I, (C.labels.level (d i)).Index

def sectionFormula {I : Type} (d : I → ℕ) (i : Slot C d) :
    Formula G (C.localSection (d i.1)).stencil :=
  (C.localSection (d i.1)).evalC (Size.axis (C.labels.level (d i.1)) i.2)

def sectionValue {I : Type} (d : I → ℕ) (i : Slot C d) {n : Side}
    (o : Site n) (U : Config G n) : ℂ :=
  (C.localSection (d i.1)).places (Size.axis (C.labels.level (d i.1)) i.2) o U

/-- The full physical coordinate, including its engineering factor. -/
def rawCoordinates (N p d : ℕ) (v : C.label d) : (C.labels.level d).Coeff :=
  ((C.S.a N : ℂ)^d)⁻¹ • (C.labels.level d).scaled
    (C.path.levels.clock.threshold N)⁻¹ (ActualPhysicalCoordinates.coordinates C N p d v)

theorem physical_as_section (N p d : ℕ) (v : C.label d)
    (o : Site (C.side N p)) (U : Config G (C.side N p)) :
    C.O N p v o U = (C.localSection d).places (rawCoordinates C N p d v) o U := by
  change ((C.S.a N : ℂ)^d)⁻¹ *
    (C.localSection d).places ((C.labels.level d).scaled
      (C.path.levels.clock.threshold N)⁻¹ ((C.factory d N p).terminal.symm v)) o U = _
  simp only [rawCoordinates, ActualPhysicalCoordinates.coordinates,
    SectionData.places, SectionData.evaluate, map_smul, smul_eq_mul]

theorem section_expansion {n : Side} (d : ℕ) (v : (C.labels.level d).Coeff)
    (o : Site n) (U : Config G n) :
    (C.localSection d).places v o U =
      ∑ k : (C.labels.level d).Index,
        v k * (C.localSection d).places (Size.axis (C.labels.level d) k) o U := by
  have h := congrArg (fun c => (C.localSection d).places c o U)
    (Size.sum_axes (C.labels.level d) v)
  simpa only [SectionData.places, SectionData.evaluate, map_sum, map_smul,
    smul_eq_mul] using h.symm

variable {I : Type} {N p : ℕ} (Q : Probes C I N p)

/-- Move the actual coordinate vector, retaining optional value conjugation. -/
def coordinates (i : I) : (C.labels.level (Q.d i)).Coeff :=
  let v := (C.labels.level (Q.d i)).act (Q.signed i).ortho
    (rawCoordinates C N p (Q.d i) (Q.z i))
  if Q.reflect i then star v else v

theorem probe_as_section (hC : C.Makes) (i : I) (U : Config G (C.side N p)) :
    Q.eval i U = (C.localSection (Q.d i)).places (coordinates C Q i) (Q.place i) U := by
  unfold Probes.eval coordinates
  rw [physical_as_section]
  rw [(C.localSection (Q.d i)).placed_signed (hC.sections (Q.d i))]
  split
  · exact ((hC.sections (Q.d i)).ordinary_real _ (expandAt (Q.place i) U)).symm
  rfl

theorem probe_expansion (hC : C.Makes) (i : I) (U : Config G (C.side N p)) :
    Q.eval i U = ∑ k : (C.labels.level (Q.d i)).Index,
      coordinates C Q i k * sectionValue C Q.d ⟨i, k⟩ (Q.place i) U := by
  rw [probe_as_section C Q hC]
  exact section_expansion C (Q.d i) (coordinates C Q i) (Q.place i) U

def cost (i : I) : ℝ := (C.labels.level (Q.d i)).coeffSize (coordinates C Q i)

theorem exact_cost (i : I) :
    (∑ k : (C.labels.level (Q.d i)).Index, ‖coordinates C Q i k‖) = cost C Q i := rfl

theorem cost_nonnegative (i : I) : 0 ≤ cost C Q i :=
  Work.G08.size_nonneg _ _

def fineProbe : Ground (Slot C Q.d × Bool) (C.side N p) := fun a =>
  if a.1 = Q.place a.2.1.1 then
    if a.2.2 then (coordinates C Q a.2.1.1 a.2.1.2).im
    else (coordinates C Q a.2.1.1 a.2.1.2).re
  else 0

theorem fineProbe_value (o : Site (C.side N p)) (i : I)
    (k : (C.labels.level (Q.d i)).Index) :
    ((fineProbe C Q (o, (⟨i, k⟩, false)) : ℝ) : ℂ) + Complex.I *
      ((fineProbe C Q (o, (⟨i, k⟩, true)) : ℝ) : ℂ) =
        if o = Q.place i then coordinates C Q i k else 0 := by
  by_cases h : o = Q.place i
  · simp only [fineProbe, h, if_true, Bool.false_eq_true, if_false]
    simpa only [mul_comm] using Complex.re_add_im (coordinates C Q i k)
  simp [fineProbe, h]

end YM.Integration.HorizonPhysicalFields
