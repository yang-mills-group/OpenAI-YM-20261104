import YM.Integration.ActualStencilFits
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon

/-! A concrete MS dictionary formed from the original Run's retained stencils.
The physical Deck selects the native film, whose real, homogeneous coordinates
are taken in the original frame.  The entire observable is the corresponding
finite linear combination of the original SectionData fields.  No independent
choice of a lift, Wick inverse, or equality from classical Fits is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalDictionary
open Function Lattice Labels
open MS MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Chart MS.Native.Studio
open MS.Local.Physical MS.Lifting MS.Theater
open WilsonComparison.Finite PhysicalNext.Repeat.Legato
open scoped BigOperators Classical Topology ContDiff

variable {G : Gauge}

/-- This is the literal native film-label construction used by Warehouse.label. -/
def filmLabel (B : Deck G) (d r : ℕ) (i : B.BIndex (d : ℤ) r) : Labels.Label G d :=
  ⟨film B i (h := d), limitH (filmW (h := d) B i).2,
    ((cinema _).mp (filmW (h := d) B i)).2.1⟩

private theorem film_label_real (B : Deck G) (d r : ℕ) (i : B.BIndex (d : ℤ) r) :
    Labels.realBar (filmLabel B d r i) = filmLabel B d r i :=
  Subtype.ext (((cinema _).mp (filmW (h := d) B i)).2.2)

private theorem film_label_grade (B : Deck G) (d r : ℕ) (i : B.BIndex (d : ℤ) r) :
    filmLabel B d r i ∈ Labels.Grade (d, r) :=
  (filmW (h := d) B i).2

def coordinates (R : Run G) (B : Deck G) (d r : ℕ) (i : B.BIndex (d : ℤ) r) :
    (R.family.labels.level d).Coeff :=
  (R.family.labels.level d).coords (filmLabel B d r i)

def weight (R : Run G) (B : Deck G) (d r : ℕ) (i : B.BIndex (d : ℤ) r)
    (j : (R.family.labels.level d).Index) : ℝ :=
  (coordinates R B d r i j).re

private theorem coordinates_real (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) :
    star (coordinates R B d r i) = coordinates R B d r i := by
  funext j
  change star (coordinates R B d r i j) = _
  rw [← (R.family.labels.level d).conj_basis, coordinates,
    LinearEquiv.symm_apply_apply, film_label_real]

theorem weight_cast (R : Run G) (B : Deck G) (d r : ℕ) (i : B.BIndex (d : ℤ) r)
    (j : (R.family.labels.level d).Index) :
    (weight R B d r i j : ℂ) = coordinates R B d r i j :=
  Complex.conj_eq_iff_re.mp (congr_fun (coordinates_real R B d r i) j)

theorem off_grade (R : Run G) (B : Deck G) (d r : ℕ) (i : B.BIndex (d : ℤ) r)
    (j : (R.family.labels.level d).Index)
    (h : (R.family.labels.level d).grades j ≠ (d, r)) :
    coordinates R B d r i j = 0 :=
  (R.family.labels.level d).power_coefficient j (Ne.symm h) (film_label_grade B d r i)

private theorem weight_zero (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) (j : (R.family.labels.level d).Index)
    (h : (R.family.labels.level d).grades j ≠ (d, r)) :
    weight R B d r i j = 0 :=
  congrArg Complex.re (off_grade R B d r i j h)

/-- The exact native law is expanded in the original frame, with no quotient projection. -/
theorem law_expansion (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) :
    B.raw (d : ℤ) r i = ∑ j : (R.family.labels.level d).Index,
      (weight R B d r i j : ℂ) •
        ActualStencilClassicalLaw.law (R.family.labels.level d) j := by
  have h : filmLabel B d r i = ∑ j : (R.family.labels.level d).Index,
      coordinates R B d r i j • (R.family.labels.level d).basis j :=
    ((R.family.labels.level d).basis.sum_repr _).symm
  calc
    _ = MS.Theater.orbit G (filmLabel B d r i).val := (lamp_here B i).symm
    _ = _ := by
      rw [h, AddSubmonoidClass.coe_finsetSum, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Submodule.coe_smul, map_smul, weight_cast, ActualStencilClassicalLaw.law]

private theorem original_aura (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) :
    Aura (∑ j : (R.family.labels.level d).Index,
      (weight R B d r i j : ℂ) • (ActualFiniteStencil.retained R d j).F) r := by
  apply Aura.sum
  intro j _
  by_cases h : (R.family.labels.level d).grades j = (d, r)
  · simpa only [h] using
      ((ActualFiniteStencil.retained R d j).aura.scalar (weight R B d r i j))
  · rw [weight_zero R B d r i j h, Complex.ofReal_zero, zero_smul]
    exact Aura.zero G r

/-- A full original-source realization, fixed before volumes, sites and coupling orders. -/
def cylinder (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) : WilsonComparison.Finite.Stencil G r where
  F := ∑ j : (R.family.labels.level d).Index,
    (weight R B d r i j : ℂ) • (ActualFiniteStencil.retained R d j).F
  O n x U := ∑ j : (R.family.labels.level d).Index,
    weight R B d r i j * (ActualFiniteStencil.retained R d j).O n x U
  continuous n x := continuous_finsetSum Finset.univ fun j _ =>
    ((ActualFiniteStencil.retained R d j).continuous n x).const_smul (weight R B d r i j)
  reads n x := by
    rw [map_sum, map_sum]
    simp only [map_smul]
    have hO :
        (∑ j : (R.family.labels.level d).Index,
          weight R B d r i j • (ActualFiniteStencil.retained R d j).O n (wrap n x)) =
        (fun U => ∑ j : (R.family.labels.level d).Index,
          weight R B d r i j * (ActualFiniteStencil.retained R d j).O n (wrap n x) U) := by
      funext U
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hO]
    exact Reads.sum Finset.univ fun j _ =>
      ((ActualFiniteStencil.retained R d j).reads n x).cash (weight R B d r i j)
  invariant n x q U := by
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (weight R B d r i j * ·)
      ((ActualFiniteStencil.retained R d j).invariant n x q U)
  low := (original_aura R B d r i).low
  phase := (original_aura R B d r i).phase

/-- The native Dictionary uses those same full original-source cylinders. -/
def dictionary (R : Run G) (B : Deck G) : Dictionary B where
  cylinder := cylinder R B
  classical_jet d r i := by
    change Fits (∑ j : (R.family.labels.level d).Index,
      (weight R B d r i j : ℂ) • (ActualFiniteStencil.retained R d j).F)
      (B.raw (d : ℤ) r i) r (d : ℤ) false
    rw [law_expansion R B d r i]
    apply Fits.sum
    intro j _
    by_cases h : (R.family.labels.level d).grades j = (d, r)
    · simpa only [h] using
        (ActualStencilFits.retained_fits R d j).smul (weight R B d r i j : ℂ)
    · rw [weight_zero R B d r i j h, Complex.ofReal_zero, zero_smul, zero_smul]
      exact Fits.zero (d : ℤ)

theorem cylinder_field (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) :
    ((dictionary R B).cylinder d r i).F =
      ∑ j : (R.family.labels.level d).Index,
        (weight R B d r i j : ℂ) • (ActualFiniteStencil.retained R d j).F := rfl

theorem cylinder_observable (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) (n : Side) (x : Site n) (U : Wilson.Config G n) :
    ((dictionary R B).cylinder d r i).O n x U =
      ∑ j : (R.family.labels.level d).Index,
        weight R B d r i j * (ActualFiniteStencil.retained R d j).O n x U := rfl

/-- Equality of the full finite observable with the original SectionData evaluation. -/
theorem original_section (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) (n : Side) (x : Site n) (U : Wilson.Config G n) :
    (((dictionary R B).cylinder d r i).O n x U : ℂ) =
      (R.family.localSection d).places (coordinates R B d r i) x U := by
  change ((∑ j : (R.family.labels.level d).Index,
    weight R B d r i j * (ActualFiniteStencil.retained R d j).O n x U : ℝ) : ℂ) = _
  calc
    _ = ∑ j : (R.family.labels.level d).Index,
        ((weight R B d r i j * (ActualFiniteStencil.retained R d j).O n x U : ℝ) : ℂ) :=
      map_sum Complex.ofRealHom _ _
    _ = ∑ j : (R.family.labels.level d).Index,
        coordinates R B d r i j *
          (ActualStencilCylinder.observed (R.family.localSection d) (Pi.single j 1) n x U : ℂ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Complex.ofReal_mul, weight_cast]
      rfl
    _ = _ := (ActualStencilCylinder.section_expansion
      (R.family.localSection d) (R.makes.sections d) (coordinates R B d r i) n x U).symm

end YM.Integration.ActualOriginalDictionary
end
