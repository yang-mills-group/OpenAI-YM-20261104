import YM.Integration.WilsonThermometerPositionFilmRecast
import YM.Integration.WilsonOriginalReceivedGradeRestriction

/-! In an arbitrary later finite recast, grade zero remembers the entire previous conditional connected reading. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramFoldedGround
open Function Finset Lattice Wilson RG Exterior Precision Tree Marker Multi
open FVA1Physical.Wilson QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise QuadraticLocal.Rebirth AllOrder AllOrder.Floe
open Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Symmetry Comparison.RG02.Order
open scoped Classical BigOperators Topology ContDiff

variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {R:Census V}
  {c f:Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(tag:S.Choices)(C:Bulk.Colors R G f)(grades:V→ℕ)
  (r:ℕ)(clock:UnitCost)(base:Bulk.Colors R G c)
local notation "bank" => FVA1Physical.Wilson.recastColors K F tag C grades r clock base
local notation "A" => Stationary.arm G c 1

theorem original (valid:∀t:Hot R,C.power t=Launch.index R grades t.val+1)(s:Hot R)(x:fieldDir G c 1):
    (Air.discharge bank 0 x).part s.val=(observe R 0 (logMarked (Bulk.Fk K F tag C x 0)) 0).part s.val:=by
  let U:=fun l (y:Stationary.Link G c)=>Orbit.words K F tag C r s.val l ((A) y)
  have root:(Air.discharge bank 0 x).part s.val=born U clock 0 r 0 ((A).symm x):=by
    rw [FVA1Physical.Wilson.recast_read K F tag C grades r clock base valid (Nat.zero_le _),Multi.part_lit];rfl
  rw [root,WilsonThermometerOriginalClockSlope.zeroth U clock r ((A).symm x)]
  dsimp only [U]
  rw [(A).apply_symm_apply]
  change (observe R r (logMarked (Bulk.Fk K F tag C x r)) 0).part s.val=_
  rw [WilsonOriginalReceivedGradeRestriction.original K F tag C x (Nat.zero_le r) 0 (Nat.zero_le 0)]

end YM.Integration.WilsonPositionProgramFoldedGround
end
