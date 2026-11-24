import YM.Integration.ActualOriginalFVAAltLibrary
import YM.FVAAlt2.Fixed

/-!
# Original-field coefficients of the finite normalized inversion quotient

Every inserted function is the retained Run's full real Dictionary field.
The Laurent shift is the sum of the actual slot orders, independently of
the engineering degrees.  The denominator is the complete original
inversion-paired Haar partition function.

This is a fixed-regulator coefficient theorem.  It does not identify the
inversion quotient with another physical measure, prove a uniform remainder,
or remove the signed defects of a different finite decomposition.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualOriginalFiniteCoefficients

open Function Lattice Wilson
open PhysicalNext.Repeat.Legato
open MS.Local.Physical
open FVAAlt2
open PertExtension.Series.Tested
open scoped Classical BigOperators

variable {G : Gauge}

/-- Every side of the original Run is a positive multiple of four. -/
theorem side_admissible (R : Run G) (N p : ℕ) :
    Pert.Orb.Admissible (R.family.side N p) := by
  have h := R.family.S.side_four N p
  exact ⟨Nat.le_of_dvd (R.family.side N p).property h,
    (show 2 ∣ 4 by decide).trans h⟩

/-- The complete original denominator is strictly positive. -/
theorem vacuum_positive (R : Run G) (N p : ℕ) (t : ℝ) :
    0 < PertExtension.Orb.preNum (G := G) (n := R.family.side N p) 1 t :=
  PertExtension.Orb.preNum_one_pos
    (even_iff_two_dvd.mpr (side_admissible R N p).2)

variable {W : Type} [LinearOrder W]
    (R : Run G) (B : Deck G) (degree rank : W → ℕ)
    (label : (w : W) → B.BIndex (degree w : ℤ) (rank w))
    (N p : ℕ) (s : Finset W) (x : W → Site (R.family.side N p))

/-- The same original real field at its actual site. -/
def field (w : W) : Config G (R.family.side N p) → ℝ :=
  ((ActualOriginalDictionary.dictionary R B).cylinder
    (degree w) (rank w) (label w)).O (R.family.side N p) (x w)

def joint : Config G (R.family.side N p) → ℝ :=
  ∏ w ∈ s, field R B degree rank label N p x w

/-- Only the true slot orders enter the Laurent normalization. -/
def slotOrder : ℕ := ∑ w ∈ s, rank w

def coefficients : ℕ → ℝ :=
  Fixed.treeMom (PertExtension.Orb.tray G)
    (joint R B degree rank label N p s x) (slotOrder rank s)

/-- The full finite numerator divided by its full vacuum, with the exact shift. -/
def normalized : ℝ → ℝ := fun t =>
  t⁻¹ ^ slotOrder rank s *
    (PertExtension.Orb.preNum (joint R B degree rank label N p s x) t /
      PertExtension.Orb.preNum (G := G) (n := R.family.side N p) 1 t)

omit [LinearOrder W] in
private theorem certified (w : W) :
    AtomCert (x w)
      ((ActualOriginalDictionary.dictionary R B).asLit.stamp
        (degree w) (rank w) (label w)) (rank w)
      (field R B degree rank label N p x w) :=
  ActualOriginalFVAAltLibrary.original_atom R B (degree w) (rank w)
    (label w) (R.family.side N p) (x w)

omit [LinearOrder W] in
private theorem continuous_field (w : W) :
    Continuous (field R B degree rank label N p x w) :=
  ((ActualOriginalDictionary.dictionary R B).cylinder
    (degree w) (rank w) (label w)).continuous (R.family.side N p) (x w)

omit [LinearOrder W] in
/-- The product is the full original SectionData evaluation, before integration. -/
theorem joint_section (U : Config G (R.family.side N p)) :
    (joint R B degree rank label N p s x U : ℂ) =
      ∏ w ∈ s, (R.family.localSection (degree w)).places
        (ActualOriginalDictionary.coordinates R B (degree w) (rank w) (label w))
        (x w) U := by
  rw [joint, Finset.prod_apply]
  change Complex.ofRealHom
    (∏ w ∈ s, field R B degree rank label N p x w U) = _
  rw [map_prod]
  exact Finset.prod_congr rfl fun w _ =>
    ActualOriginalDictionary.original_section R B (degree w) (rank w)
      (label w) (R.family.side N p) (x w) U

/-- All coefficients of the actual normalized finite expectation. -/
theorem finite_asymptotic :
    Aspiration (normalized R B degree rank label N p s x)
      (coefficients R B degree rank label N p s x) := by
  dsimp only [normalized, coefficients, joint, slotOrder]
  letI : Module.Free ℝ (SchemeRG11.Sway.Land G (R.family.side N p)) :=
    Module.Free.of_divisionRing ℝ (SchemeRG11.Sway.Land G (R.family.side N p))
  let A := Module.finBasis ℝ (SchemeRG11.Sway.Land G (R.family.side N p))
  let b := Module.finBasis ℝ (ScalarGhost G (R.family.side N p))
  exact
    Fixed.preExpectation (PertExtension.Orb.traySpec G) A b s
      (side_admissible R N p) (certified R B degree rank label N p x)
      (fun w _ => continuous_field R B degree rank label N p x w)

/-- No different coefficient sequence has the same normalized finite asymptotic. -/
theorem finite_unique (a : ℕ → ℝ)
    (h : Aspiration (normalized R B degree rank label N p s x) a) :
    a = coefficients R B degree rank label N p s x :=
  h.unique (finite_asymptotic R B degree rank label N p s x)

/-- The reconstructed full Wick quotient has these same coefficients for every
finite choice of Landau and ghost coordinates. -/
theorem wick_coefficient {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Module.Basis ι ℝ (SchemeRG11.Sway.Land G (R.family.side N p)))
    (b : Module.Basis κ ℝ (ScalarGhost G (R.family.side N p))) (m : ℕ) :
    PowerSeries.coeff m
      (SchemeRG11.Sway.Lentry
        (Fixed.total A (certified R B degree rank label N p x) s)) =
      (coefficients R B degree rank label N p s x m : ℂ) := by
  exact Fixed.per (PertExtension.Orb.traySpec G) A b s
    (side_admissible R N p) (certified R B degree rank label N p x) m

/-- The independent finite RG10 input calculation, at the exact shifted order. -/
theorem RG10_coefficient (m : ℕ) :
    let he := even_iff_two_dvd.mpr (side_admissible R N p).2
    let O := PertExtension.Orb.restrictedO (joint R B degree rank label N p s x)
    PowerSeries.coeff (m + slotOrder rank s)
      ((FormalOPE.RG10.InversionTop.feed he).step
        (FormalOPE.RG10.InversionTop.vertices G (R.family.side N p))
        (FormalOPE.RG10.InversionTop.raw O)) =
      (coefficients R B degree rank label N p s x m : ℂ) := by
  exact Fixed.RG10_at s (side_admissible R N p)
    (certified R B degree rank label N p x)
    (fun w _ => continuous_field R B degree rank label N p x w) m

end YM.Integration.ActualOriginalFiniteCoefficients
end
