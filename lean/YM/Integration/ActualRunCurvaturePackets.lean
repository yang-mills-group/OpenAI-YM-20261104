import YM.Integration.NativeCurvatureTensor
import YM.Integration.ActualRunGradedKernels
import YM.PertExtension.PaintTop

/-!
The same Run's original section, expressed by finite invariant curvature
tensors. The representation is selected from R and the engineering horizon
before the cutoff, position, coordinate vector or test data. All monomials,
original stencil inclusions, minimum field grades and threshold powers remain
literal. This is the unmasked analytic section; mask compensation and the
countable regular remainder at later flow stages are separate.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunCurvaturePackets

open Function Finset Lattice Wilson RG Source Labels
open PertExtension
open PhysicalNext.Repeat.Legato
open NativeCurvatureTensor
open scoped Classical BigOperators

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}

structure Presentation (S : SectionData F) where
  data : Heat.Top.Rendered F
  valid : Heat.Top.Valid data.toData S
  within (i : F.Index) (j : Fin (data.count i)) :
    (data.columns i j).stencil ⊆ S.stencil
  anchored : 0 ∈ S.stencil

def ofSection (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (hp : Bid.pop S) : Presentation S := by
  choose count columns within shape equal low using hp
  let E : Heat.Top.Data F := ⟨count, columns, shape, low⟩
  exact ⟨E.color, Heat.Top.color_acts E equal hS, within, hS.anchored⟩

variable {S : SectionData F} (D : Presentation S)

def basisValue (i : F.Index) {n : Side} (o : Site n) (U : Config G n) : ℂ :=
  ∑ m ∈ (D.data.shape i).support, MvPolynomial.coeff m (D.data.shape i) *
    value (fun k => (word m k).2)
      (fun k => (D.data.columns i (word m k).1).atSite U o)

private theorem cover_basis (i : F.Index) (U : CoverConfig G) :
    S.evaluate (Pi.single i 1) U =
      ∑ m ∈ (D.data.shape i).support, MvPolynomial.coeff m (D.data.shape i) *
        value (fun k => (word m k).2)
          (fun k => (D.data.columns i (word m k).1).eval U) := by
  rw [D.valid i]
  exact polynomial_value (D.data.shape i) (D.data.fixed i)
    (Bid.mapped (D.data.columns i) U)

theorem placed_basis (i : F.Index) {n : Side} (o : Site n) (U : Config G n) :
    S.places (Pi.single i 1) o U = basisValue D i o U := by
  exact cover_basis D i (expandAt o U)

theorem basis_footprint (i : F.Index)
    (m : (Fin (D.data.count i) × G.ColorIndex) →₀ ℕ) {n : Side} (o : Site n) :
    (⟨(fun k => D.data.columns i (word m k).1), fun _ => 0⟩ :
      Atom G (m.sum fun _ r => r)).footprint o ⊆ S.footprint o := by
  apply Finset.image_subset_image
  apply Finset.insert_subset D.anchored
  intro z hz
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hz
  exact D.within i (word m k).1 hk

def ofRun (R : Run G) (d : ℕ) : Presentation (R.family.localSection d) :=
  ofSection (R.family.localSection d) (R.makes.sections d)
    (ActualRunGradedKernels.section_valuation R d)

theorem run_field (R : Run G) (L p d : ℕ) (x : Site (R.family.side L p))
    (j : (R.family.labels.level d).Index) (U : Config G (R.family.side L p)) :
    (ActualRunGradedKernels.field R L p d x j U : ℂ) =
      basisValue (ofRun R d) j x U := by
  change (ActualStencilCylinder.observed (R.family.localSection d) (Pi.single j 1)
    (R.family.side L p) x U : ℂ) = _
  rw [ActualStencilCylinder.observed_complex (R.family.localSection d)
    (R.makes.sections d) j (R.family.side L p) x U]
  exact placed_basis (ofRun R d) j x U

theorem run_physical (R : Run G) (L p d : ℕ) (x : Site (R.family.side L p))
    (j : (R.family.labels.level d).Index) (U : Config G (R.family.side L p)) :
    ((R.family.S.a L ^ d : ℝ) : ℂ) *
      R.family.O L p
        (Dict06.Actual.calibrate R.family L p d
          ((R.family.labels.level d).basis j)) x U =
      basisValue (ofRun R d) j x U := by
  rw [← ActualRunGradedKernels.field_physical R L p d x j U]
  exact run_field R L p d x j U

theorem run_kernel (R : Run G) (N p L d : ℕ) (v : R.family.label d)
    (x : Site (R.family.side L p)) (U : Config G (R.family.side L p)) :
    ActualRunPhysicalPages.kernel R N p L d v x U =
      ∑ j : (R.family.labels.level d).Index,
        ((((R.family.path.rep N p L).p.threshold)⁻¹ ^
          ActualRunGradedKernels.rank R d j : ℝ) : ℂ) *
          v j * basisValue (ofRun R d) j x U := by
  rw [ActualRunGradedKernels.kernel_expansion R L p d N v x U]
  apply Finset.sum_congr rfl
  intro j _
  rw [run_field]

end YM.Integration.ActualRunCurvaturePackets
