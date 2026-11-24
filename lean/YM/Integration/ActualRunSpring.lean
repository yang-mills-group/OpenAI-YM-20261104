import YM.Integration.RunPhysicalMarks

/-!
The native Spring already retained by a Run, before any marker census, test
family or Taylor order is supplied.  Both endpoint equalities are equalities
of the complete representations.  In particular the output activities and
coupling are those of the next original Run input.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunSpring

open Function Set Lattice Wilson RG RG.Shoot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open PhysicalNext.Repeat.Roof
open Pressure Testing Input Precision Org Supply Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe
open MergeProof
open scoped Classical

variable {G : Gauge} (R : Run G) (N p m : ℕ) (hm : m < N)

/-- The original native witness carried by this Run's actual door.  No
representation is reconstructed merely from equality of evaluated density. -/
structure Packet where
  lower : ℝ
  upper : ℝ
  input : UVNext.CouplingReset.In R.alloy.B.a m p
  spring : Spring R.kit N m p lower upper input
  point : Set.Icc lower upper
  coarse : R.family.path.rep N p m = spring.result point.val
  fine : R.family.path.rep N p (m + 1) = input point.val
  door : R.doors N p m hm = duet R.family.path N p m coarse fine
    (sandboxK spring point)

/-- This witness comes from the retained native construction, rather than a
new invocation of Spring.faces. -/
theorem packet_exists : Nonempty (Packet R N p m hm) := by
  obtain ⟨l, v, Q, U, x, he, ht, hD⟩ := R.carries N m p hm
  exact ⟨⟨l, v, Q, U, x, he, ht, hD⟩⟩

/-- A choice depending only on the Run and its original step indices. -/
def selected : Packet R N p m hm :=
  Classical.choice (packet_exists R N p m hm)

namespace Packet

variable {R N p m hm} (P : Packet R N p m hm)

/-- Every activity field, including every Nat forced row and extraTest,
is transported by the literal incoming representation equality. -/
theorem input_activities :
    (P.input P.point.val).activities =
      (R.family.path.rep N p (m + 1)).activities :=
  congrArg (fun V => V.activities) P.fine.symm

/-- The complete output activities are the next original Run activities. -/
theorem output_activities :
    (P.spring.result P.point.val).activities =
      (R.family.path.rep N p m).activities :=
  congrArg (fun V => V.activities) P.coarse.symm

theorem input_beta : (P.input P.point.val).beta =
    (R.family.path.rep N p (m + 1)).beta :=
  congrArg (fun V => V.beta) P.fine.symm

theorem output_beta : (P.spring.result P.point.val).beta =
    (R.family.path.rep N p m).beta :=
  congrArg (fun V => V.beta) P.coarse.symm

/-- The canonical native output has the actual next beta-band receipt;
this does not infer a band from a density equality or a small mismatch. -/
theorem output_band :
    (P.spring.result P.point.val).beta ∈ band R.alloy.B.a m := by
  rw [← P.coarse]
  exact ((R.T.sticks N p).prices m (Nat.zero_le _) hm.le).2

theorem output_lives :
    Lives R.alloy.B.bake N m p (P.spring.result P.point.val) := by
  rw [← P.coarse]
  exact ((R.T.sticks N p).prices m (Nat.zero_le _) hm.le).1

theorem input_slots :
    HasSlots (P.input P.point.val).p (P.input P.point.val).activities := by
  rw [← P.fine]
  exact RunPhysicalMarks.actual_hasSlots R N p (m + 1) hm

theorem output_slots :
    HasSlots (P.spring.result P.point.val).p
      (P.spring.result P.point.val).activities := by
  rw [← P.coarse]
  exact RunPhysicalMarks.actual_hasSlots R N p m hm.le

include P in
/-- Original recipe Move, on the original cutoff and both actual endpoints. -/
theorem actual_move (hG : G.Simple) :
    R.alloy.B.Move N m p (R.family.path.rep N p m)
      (R.family.path.rep N p (m + 1)) := by
  have h := ((P.spring.moves hG hm).2 P.point.val P.point.property).1
  rw [← P.coarse, ← P.fine] at h
  exact h

/-- The native output of step i+1 is admitted at the immediately following
step i.  Both sides use the literal same lattice index, without a carrier cast
or an extra admission hypothesis. -/
theorem next_intake {i : ℕ} {hStep : i + 1 < N}
    (Q : Packet R N p (i + 1) hStep) :
    Intake (Pane.asks R.alloy i) (ships R.alloy.B N i p)
      (R.family.path.levels.clock.hatBeta i)
      (Q.spring.result Q.point.val) := by
  rw [← Q.coarse]
  exact RunPhysicalMarks.actual_intake R N p i (by omega)

end Packet

/-- Adjacent native witnesses glue as complete representations on the same
cutoff and period.  Their test families need not be identified. -/
theorem adjacent {R : Run G} {N p i : ℕ}
    {hUpper : i + 1 < N} {hLower : i < N}
    (P : Packet R N p (i + 1) hUpper)
    (Q : Packet R N p i hLower) :
    P.spring.result P.point.val = Q.input Q.point.val :=
  P.coarse.symm.trans Q.fine

end YM.Integration.ActualRunSpring
