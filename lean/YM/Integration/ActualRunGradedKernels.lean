import YM.Integration.ActualStencilCylinder
import YM.Integration.ActualRunPhysicalPages

/-!
The original finite graded basis of each actual unmasked input kernel.
The rank is the basis element's number of fields, not the enclosing frame
horizon.  Every threshold power and every complex coordinate is retained.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunGradedKernels

open Function Finset Lattice Wilson RG Source Labels
open PhysicalNext.Repeat.Legato
open MS.Cylinder.Taylor MS.Book
open scoped Classical ContDiff BigOperators

variable {G : Gauge} (R : Run G) (L p d : ℕ)

abbrev rank (j : (R.family.labels.level d).Index) : ℕ :=
  ((R.family.labels.level d).grades j).2

def field (x : Site (R.family.side L p))
    (j : (R.family.labels.level d).Index)
    (U : Config G (R.family.side L p)) : ℝ :=
  ActualStencilCylinder.observed (R.family.localSection d) (Pi.single j 1)
    (R.family.side L p) x U

/-- This is the canonical section already contained in the same Run. -/
theorem section_valuation : Bid.pop (R.family.localSection d) := by
  change Bid.pop (Next.Foundations.localSection G d)
  exact Next.Foundations.valuation G d

theorem rank_pos (j : (R.family.labels.level d).Index) (hj : j ≠ 0) :
    0 < rank R d j :=
  (R.family.labels.level d).factors_pos j hj

/-- The real basis field equals the original physical calibrated operator,
with its full original engineering factor. -/
theorem field_physical (x : Site (R.family.side L p))
    (j : (R.family.labels.level d).Index)
    (U : Config G (R.family.side L p)) :
    (field R L p d x j U : ℂ) =
      ((R.family.S.a L ^ d : ℝ) : ℂ) *
        R.family.O L p
          (Dict06.Actual.calibrate R.family L p d
            ((R.family.labels.level d).basis j)) x U := by
  have ha : (R.family.S.a L : ℂ) ^ d ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos L).ne')
  have hS : (R.family.localSection d).Sound R.family.params := R.makes.sections d
  unfold field
  rw [ActualStencilCylinder.observed_complex (R.family.localSection d) hS j
    (R.family.side L p) x U,
    Dict06.Actual.names, Dict06.Actual.meet,
    (R.family.labels.level d).coords_basis, Complex.ofReal_pow]
  unfold Dict06.Actual.factor SectionData.places
  rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

theorem field_chart (x : Site (R.family.side L p))
    (j : (R.family.labels.level d).Index) :
    ContDiff ℝ ω (fun A : Directions G (R.family.side L p) =>
      field R L p d x j (increment 1 A)) := by
  unfold field ActualStencilCylinder.observed SectionData.places SectionData.evaluate
  exact Complex.reCLM.contDiff.comp
    (ActualStencilAnalytic.polynomial x
      ((R.family.localSection d).evalC (Pi.single j 1)) 1)

/-- The native analytic-series rank holds in every specified real linear
chart, with no new vanishing premise on the Run. -/
theorem field_low {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E →L[ℝ] Directions G (R.family.side L p)) (e : A → E)
    (x : Site (R.family.side L p)) (j : (R.family.labels.level d).Index) :
    From (ink e ((fun B : Directions G (R.family.side L p) =>
      field R L p d x j (increment 1 B)) ∘ T)) (rank R d j : ℤ) := by
  have he : ((fun B : Directions G (R.family.side L p) =>
      field R L p d x j (increment 1 B)) ∘ T) =
      (R.family.S.a L ^ d) •
        (ActualStencilJetFloor.realChart R.family L p d x j ∘ T) := by
    funext a
    have h := congrArg Complex.re (field_physical R L p d x j (increment 1 (T a)))
    simpa only [comp_apply, Pi.smul_apply, smul_eq_mul,
      ActualStencilJetFloor.realChart, ActualStencilJetFloor.chart,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, sub_zero] using h
  rw [he, ink_smul e
    ((ActualStencilJetFloor.realChart_analytic R.family L p d x j).contDiffAt.comp
      0 T.contDiff.contDiffAt)]
  intro l hl
  change ((R.family.S.a L ^ d : ℝ) : ℂ) *
    ink e (ActualStencilJetFloor.realChart R.family L p d x j ∘ T) l = 0
  rw [ActualStencilJetFloor.realChart_low_comp R.family L p d T e
    (section_valuation R d) x j l hl, mul_zero]

theorem field_envelope (x : Site (R.family.side L p))
    (j : (R.family.labels.level d).Index) :
    Envelope (field R L p d x j) := by
  have h := Envelope.compactC
    ((R.family.localSection d).continuous_places (Pi.single j 1) x)
  obtain ⟨c, hc⟩ := h.cost
  refine ⟨Complex.measurable_re.comp h.meas, c, fun U => ?_⟩
  exact (Complex.abs_re_le_norm _).trans (hc U)

/-- Exact arbitrary-coordinate reconstruction, before any test-dependent
choice.  The actual outer cutoff enters only its original threshold. -/
theorem kernel_expansion (N : ℕ) (v : R.family.label d)
    (x : Site (R.family.side L p)) (U : Config G (R.family.side L p)) :
    ActualRunPhysicalPages.kernel R N p L d v x U =
      ∑ j : (R.family.labels.level d).Index,
        ((((R.family.path.rep N p L).p.threshold)⁻¹ ^ rank R d j : ℝ) : ℂ) *
          v j * (field R L p d x j U : ℂ) := by
  change (R.family.localSection d).places
    ((R.family.labels.level d).scaled
      (R.family.path.rep N p L).p.threshold⁻¹ v) x U = _
  have hS : (R.family.localSection d).Sound R.family.params := R.makes.sections d
  exact ActualStencilCylinder.section_expansion (R.family.localSection d) hS
    ((R.family.labels.level d).scaled (R.family.path.rep N p L).p.threshold⁻¹ v)
    (R.family.side L p) x U

end YM.Integration.ActualRunGradedKernels
