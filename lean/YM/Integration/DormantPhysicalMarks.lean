import YM.Integration.RegisteredPhysicalMarks

/-! Register independent literal stencils using the permanent dormant rows in
an existing physical alphabet. No representation or density is changed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.DormantPhysicalMarks

open Function Lattice Wilson RG
open PhysicalNext.Repeat Push.AbsoluteSums.Animals
open Progress.DirectedRecipe RemainderComparison RemainderComparison.Typeface
open RemainderComparison.Placement
open scoped BigOperators Classical

variable {G : Gauge}

/-- A permanent label for each independent test slot. Its numerical value is
irrelevant; injectivity keeps colliding geometric supports as distinct marks. -/
def testCode (ι : Type) [Countable ι] : ι ↪ ℕ :=
  ⟨(Countable.exists_injective_nat ι).choose,
    (Countable.exists_injective_nat ι).choose_spec⟩

/-- Reserve an already dormant row in the existing physical alphabet. -/
def dormantSlot {f : Side} {ι : Type} [Countable ι]
    (radii : ι → ℕ) (positions : ι → Site f) (i : ι) : ℕ :=
  blankRow f (Tile.aperture (positions i) (radii i), testCode ι i)

theorem dormantSlot_injective {f : Side} {ι : Type} [Countable ι]
    (radii : ι → ℕ) (positions : ι → Site f) :
    Injective (dormantSlot radii positions) := by
  intro i j h
  apply (testCode ι).injective
  exact congr_arg Prod.snd ((blankRow f).injective h)

/-- Registration occurs on R itself: no extension, density replacement, or
extra registration hypothesis is used beyond the retained alphabet. -/
theorem dormant_registration {f : Side} {R : Rep G f}
    (hR : HasSlots R.p R.activities) {ι : Type} [Countable ι]
    (radii : ι → ℕ) (positions : ι → Site f) (i : ι) :
    R.activities.reg (dormantSlot radii positions i) =
      Tile.aperture (positions i) (radii i) ∧
    R.activities.E (dormantSlot radii positions i) = 0 := by
  refine ⟨?_, hR.regular _⟩
  rw [hR.reg]
  exact congr_arg Prod.fst (recorded (regularKeys f)
    (Tile.aperture (positions i) (radii i)) (testCode ι i))

/-- A retained fixed alphabet directly supports independent literal portraits.
This uses the given representation itself and its existing zero rows. -/
theorem portraits {f : Side} (R : Rep G f) (hR : HasSlots R.p R.activities)
    (hβ : 0 < R.beta) {ι : Type} [Countable ι]
    {E : ι → Type*} {orders radii : ι → ℕ} {costs : ι → ℝ}
    (D : ∀ i, Tile G (E i) (orders i) (radii i) (costs i))
    (base : ∀ i, E i) (positions : ι → Site f) :
    ∃ M : ∀ i, Portrait R (E i),
      (∀ i, (M i).wing = Lotus.Wing.logKey (dormantSlot radii positions i)) ∧
      (∀ i, (M i).weight = Tile.peso G (orders i) (radii i) (costs i) R.p) ∧
      ∀ tests i, ((independentPortraits M i).angle tests).ingredient =
        masked R.p.threshold (neighbors (radii i) (positions i))
          (Tile.read (D i) (positions i) (tests i)) :=
  registered_independent_portraits R D base positions (dormantSlot radii positions) hβ
    (fun i => (dormant_registration hR radii positions i).1)
    (fun i => (dormant_registration hR radii positions i).2)

end YM.Integration.DormantPhysicalMarks
