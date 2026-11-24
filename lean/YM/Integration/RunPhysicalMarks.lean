import YM.Integration.DormantPhysicalMarks
import YM.FullVolume.Cross

/-! Physical admission and literal independent mark registration on any given
actual Run. No new Run or Family is selected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.RunPhysicalMarks

open Function Lattice Wilson RG RG.Shoot
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Roof
open Pressure Testing Input Precision Org Supply Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe
open Push.AbsoluteSums.Animals
open RemainderComparison RemainderComparison.Typeface RemainderComparison.Placement
open scoped BigOperators Classical

variable {G : Gauge}

/-- The unchanged actual Run trajectory already has every dormant row.
This uses its original Bolt.sticks Lives certificate, not equality of
evaluated densities. -/
theorem actual_hasSlots (R : Run G)
    (N n m : ℕ) (hm : m ≤ N) :
    HasSlots (R.family.path.rep N n m).p (R.family.path.rep N n m).activities := by
  have hL := ((R.T.sticks N n).prices m (Nat.zero_le _) hm).1
  have hR := hL.loads
  rw [R.kit.machine.ready] at hR
  change HasSlots (R.T.history N n m).p (R.T.history N n m).activities
  rw [hL.point]
  exact (PeriodFuture.pockets hR).2.2.2.2

/-- The actual Run itself satisfies the next physical Intake receipt. -/
theorem actual_intake (R : Run G)
    (N n m : ℕ) (hm : m < N) :
    Intake (Pane.asks R.alloy m) (ships R.alloy.B N m n)
      (R.family.path.levels.clock.hatBeta m) (R.family.path.rep N n (m+1)) := by
  have h := (R.T.sticks N n).prices (m+1) (Nat.zero_le _) hm
  exact Application.intake_at R.alloy.B N m n hm _ h.1 h.2

/-- Literal independent marks can be attached in place on the common actual
Run family at every level, including its top input. -/
theorem actual_portraits (R : Run G)
    (N n m : ℕ) (hm : m ≤ N) {ι : Type} [Countable ι] {E : ι → Type*}
    {orders radii : ι → ℕ} {costs : ι → ℝ}
    (D : ∀ i, RemainderComparison.Placement.Tile G (E i) (orders i) (radii i) (costs i))
    (base : ∀ i, E i) (positions : ι → Site (R.family.side m n)) :
    ∃ M : ∀ i, RemainderComparison.Typeface.Portrait (R.family.path.rep N n m) (E i),
      (∀ i, (M i).wing = Lotus.Wing.logKey (DormantPhysicalMarks.dormantSlot radii positions i)) ∧
      (∀ i, (M i).weight = RemainderComparison.Placement.Tile.peso G
        (orders i) (radii i) (costs i) (R.family.path.rep N n m).p) ∧
      ∀ tests i, ((independentPortraits M i).angle tests).ingredient =
        masked (R.family.path.rep N n m).p.threshold (neighbors (radii i) (positions i))
          (RemainderComparison.Placement.Tile.read (D i) (positions i) (tests i)) :=
  DormantPhysicalMarks.portraits _ (actual_hasSlots R N n m hm)
    (Overlay.beta_positive R.makes.wilson hm) D base positions

/-- The full joint marked density on the original actual representation.
Distinct tests remain distinct even when their geometric supports coincide. -/
theorem actual_marked_density (R : Run G)
    (N n m : ℕ) {c : Side}
    (S : StepData c (R.family.side m n)) {ι : Type} [Fintype ι]
    {E : ι → Type*} {orders radii : ι → ℕ} {costs : ι → ℝ}
    (D : ∀ i, Tile G (E i) (orders i) (radii i) (costs i))
    (base : ∀ i, E i) (positions : ι → Site (R.family.side m n)) (hm : m ≤ N)
    {V : Type} [DecidableEq V] (B : Marker.Census V) (z : ι → Marker.Poly B) :
    ∃ M : ∀ i, Portrait (R.family.path.rep N n m) (E i),
      (∀ i, (M i).wing = Lotus.Wing.logKey (DormantPhysicalMarks.dormantSlot radii positions i)) ∧
      (∀ i, (M i).weight = Tile.peso G (orders i) (radii i) (costs i)
        (R.family.path.rep N n m).p) ∧
      ∀ (tests : ∀ i, E i) (U : Config G (R.family.side m n)),
        Serif.TuneR (brand (independentPortraits M) tests) Set.univ (fun _ => 1) 0 z S U =
          ((R.family.path.rep N n m).eval U : ℂ) • ∏ i, (1 +
            ((masked (R.family.path.rep N n m).p.threshold (neighbors (radii i) (positions i))
              (Tile.read (D i) (positions i) (tests i)) U : ℝ) : ℂ) • z i) := by
  exact registered_marked_density (R.family.path.rep N n m) S B z D base positions
    (DormantPhysicalMarks.dormantSlot radii positions) (DormantPhysicalMarks.dormantSlot_injective radii positions)
    (Overlay.beta_positive R.makes.wilson hm)
    (fun i => (DormantPhysicalMarks.dormant_registration (actual_hasSlots R N n m hm) radii positions i).1)
    (fun i => (DormantPhysicalMarks.dormant_registration (actual_hasSlots R N n m hm) radii positions i).2)

end YM.Integration.RunPhysicalMarks
