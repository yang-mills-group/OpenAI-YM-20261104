import YM.Integration.ActualOriginalDictionary
import YM.FVAAlt2.Library

/-! A literal FVAAlt2 library for the original Run's fields.

The library is fixed before the period, insertion sites and perturbative order.
Its fields are the original Dictionary's full real observables.  The placed-field
identity uses the original SectionData translation law, not equality of Taylor
tables.  Global continuity is retained for the normalized finite expectation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalFVAAltLibrary
open Function Lattice
open MS MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Chart MS.Native.Sew
open MS.Native.Studio MS.Local.Physical
open WilsonComparison.Finite PhysicalNext.Repeat.Legato
open FVAAlt2 FVAAlt2.Billing
open scoped Topology ContDiff

variable {G : Gauge}

private theorem origin_germ {r : ℕ} (C : Stencil G r) (n : Side) :
    MS.Cylinder.Taylor.germ (C.O n 0 ∘ nation) := by
  simpa only [map_zero] using (C.reads n 0).born

private theorem origin_enters {r : ℕ} (C : Stencil G r) (n : Side) :
    enters n C.F = MS.Native.reads (C.O n 0 ∘ nation) := by
  convert (C.reads n 0).home using 1
  · rw [shift_nil]
    rfl
  rw [map_zero]

/-- Use each supplied full observable at its origin, without choosing a new lift. -/
def fromDictionary {B : Deck G} (D : Dictionary B) : Library D.asLit where
  final d r i n := (D.cylinder d r i).O n 0
  ok d r i n x :=
    AtomCert.on_aura x (D.cylinder d r i).F (D.cylinder d r i).aura
      ((D.cylinder d r i).O n 0) ((D.cylinder d r i).invariant n 0)
      (origin_germ (D.cylinder d r i) n) (origin_enters (D.cylinder d r i) n)

theorem fromDictionary_continuous {B : Deck G} (D : Dictionary B)
    (d r : ℕ) (i : B.BIndex (d : ℤ) r) (n : Side) :
    Continuous ((fromDictionary D).final d r i n) :=
  (D.cylinder d r i).continuous n 0

/-- The same original Run and original film coordinates supply every volume. -/
abbrev original (R : Run G) (B : Deck G) :
    Library (ActualOriginalDictionary.dictionary R B).asLit :=
  fromDictionary (ActualOriginalDictionary.dictionary R B)

theorem original_section (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) (n : Side) (U : Wilson.Config G n) :
    (((original R B).final d r i n U : ℝ) : ℂ) =
      (R.family.localSection d).places
        (ActualOriginalDictionary.coordinates R B d r i) 0 U :=
  ActualOriginalDictionary.original_section R B d r i n 0 U

/-- Full equality at every field configuration and every site. -/
theorem original_translate (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) (n : Side) (x : Site n) :
    moveLetter x ((original R B).final d r i n) =
      ((ActualOriginalDictionary.dictionary R B).cylinder d r i).O n x := by
  funext U
  have htranslate : U ∘ turnAddress x = translate x U := by
    funext e
    change U (x + e.1, e.2) = U (e.1 + x, e.2)
    rw [add_comm x e.1]
  apply Complex.ofReal_injective
  change
    ((((ActualOriginalDictionary.dictionary R B).cylinder d r i).O
      n 0 (U ∘ turnAddress x) : ℝ) : ℂ) =
    ((((ActualOriginalDictionary.dictionary R B).cylinder d r i).O
      n x U : ℝ) : ℂ)
  rw [htranslate, ActualOriginalDictionary.original_section,
    ActualOriginalDictionary.original_section]
  simpa only [zero_add] using
    (R.family.localSection d).places_trans
      (ActualOriginalDictionary.coordinates R B d r i) (0 : Site n) x U

/-- The actual placed original field discharges every AtomCert input. -/
theorem original_atom (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) (n : Side) (x : Site n) :
    AtomCert x ((ActualOriginalDictionary.dictionary R B).asLit.stamp d r i) r
      (((ActualOriginalDictionary.dictionary R B).cylinder d r i).O n x) := by
  simpa only [original_translate] using (original R B).ok d r i n x

theorem original_placed_continuous (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) (n : Side) (x : Site n) :
    Continuous (moveLetter x ((original R B).final d r i n)) := by
  rw [original_translate]
  exact ((ActualOriginalDictionary.dictionary R B).cylinder d r i).continuous n x

/-- The library's placed field is the full original SectionData evaluation. -/
theorem original_placed_section (R : Run G) (B : Deck G) (d r : ℕ)
    (i : B.BIndex (d : ℤ) r) (n : Side) (x : Site n)
    (U : Wilson.Config G n) :
    ((moveLetter x ((original R B).final d r i n) U : ℝ) : ℂ) =
      (R.family.localSection d).places
        (ActualOriginalDictionary.coordinates R B d r i) x U := by
  rw [original_translate]
  exact ActualOriginalDictionary.original_section R B d r i n x U

end YM.Integration.ActualOriginalFVAAltLibrary
end
