import YM.WilsonBridge.Principal
import YM.Integration.ActualFiniteStencil
import YM.Integration.ActualStencilClassicalLaw

/-! The native momentum Fits theorem for the literal retained cylinder.
The independently realized coreK is identified by all finite-volume Taylor
coefficients; no new section, Survey, or comparison premise is introduced.
This is the classical momentum-jet condition, not an infrared estimate for
the normalized quantum quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStencilFits
open Function Filter Lattice Wilson Source Labels
open MS MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Chart
open PhysicalNext.Repeat.Legato
open scoped Classical Topology

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}

theorem basis_enter (S : SectionData F) (i : F.Index) (n : Side) :
    enters n (ActualStencilCylinder.cylinder S (Pi.single i 1)) =
      MS.Native.reads (ActualStencilCylinder.observed S (Pi.single i 1) n 0 ∘ nation) := by
  change (shown n (ActualStencilCylinder.cylinder S (Pi.single i 1))).val = _
  have h := (ActualStencilCylinder.reads S (Pi.single i 1) n 0).home
  simpa only [Lab.shift_nil, map_zero] using h

/-- Both realizations are the same cover cylinder because their original
finite-volume observables have exactly the same Taylor coefficients. -/
theorem core_eq (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (hV : Bid.pop S) (i : F.Index) :
    WilsonBridge.Wisdom.coreK hS hV i =
      ActualStencilCylinder.cylinder S (Pi.single i 1) := by
  apply (Lab.enterEq _ _).mp
  refine Eventually.of_forall fun n => ?_
  rw [WilsonBridge.Wisdom.answers, basis_enter]
  rfl

/-- The actual original field has the native classical momentum jet of its
original homogeneous frame polynomial, with its original two grades. -/
theorem basis_fits (S : SectionData F) {H : Hol G} (hS : S.Sound H)
    (hV : Bid.pop S) (i : F.Index) :
    MS.Lifting.Fits (ActualStencilCylinder.cylinder S (Pi.single i 1))
      (ActualStencilClassicalLaw.law F i) (F.grades i).2 (F.grades i).1 false := by
  rw [← core_eq S hS hV i]
  exact WilsonBridge.Glyphs.brightK i hS hV

theorem original_fits (C : Family G) (hC : C.Makes) (d : ℕ)
    (hV : Bid.pop (C.localSection d)) (i : (C.labels.level d).Index) :
    MS.Lifting.Fits (ActualFiniteStencil.original C hC d hV i).F
      (ActualStencilClassicalLaw.law (C.labels.level d) i)
      ((C.labels.level d).grades i).2 ((C.labels.level d).grades i).1 false :=
  basis_fits (C.localSection d) (hC.sections d) hV i

/-- The existing Run supplies the actual valuation; the finite-MS stencil
and its physical observable remain the already retained ones. -/
theorem retained_fits (R : Run G) (d : ℕ)
    (i : (R.family.labels.level d).Index) :
    MS.Lifting.Fits (ActualFiniteStencil.retained R d i).F
      (ActualStencilClassicalLaw.law (R.family.labels.level d) i)
      ((R.family.labels.level d).grades i).2
      ((R.family.labels.level d).grades i).1 false :=
  original_fits R.family R.makes d (CoefficientBridge.run_valuation R d) i

end YM.Integration.ActualStencilFits
