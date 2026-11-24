import YM.Integration.ActualGroundContraction
import YM.Integration.PhysicalProgramRoot

/-!
# The original fixed-field ground difference at physical program roots

Every surviving pattern retains an explicit physical port. Its vertex
roots the full original pairing program, and its label lies in Unit.
The fixed physical direction, original covariance, full geometric
function, normalized tensors and outer factorial are unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualAnchoredGround

open Finset Function
open YM.RG YM.Precision YM.Lattice YM.Wilson YM.Exterior YM.Tree
open YM.Marker YM.Multi YM.Next.Rank YM.Next.SectorChange
open YM.Comparison.RG02 YM.Comparison.RG02.Order
open YM.Comparison.RG02.Cumulants
open YM.Integration.NormalizedKernelProgram (vertex)
open YM.Integration.PhysicalProgramRoot
open scoped BigOperators ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip}
  {P : PathData G} {O : ChartRatio G}
variable (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (w : S.Choices)
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable (W : Bulk.Colors R G f) (r : ℕ)

def program (n : ℕ) (B : fieldDir G c 1) : ℂ :=
  (n.factorial : ℂ)⁻¹ *
    ∑ s ∈ shards (Board R r) (Join.pair R.quiet (pick r n)),
      anchoredMode (ActualGroundProgram.coupling F) (Bulk.hinge F)
        (ActualGroundContraction.rayMap K F B)
        (vertex W.power (Bulk.markFn S F W) (Bulk.geometric K F w W) r)
        (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank
          (K.covariance F w) (K.symm F w)) (fun _ => 1) s

theorem ground_centered {n : ℕ} (hn : 0 < n) (hnr : n ≤ r)
    (B : fieldDir G c 1) :
    Symmetry.Orbit.ground K F w W r n B -
        Symmetry.Orbit.ground K F w W r n 0 = program K F w W r n B := by
  rw [ActualGroundContraction.ground_centered K F w W r hn hnr B]
  unfold ActualGroundContraction.centeredProgram program
  apply congrArg ((n.factorial : ℂ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro s _
  exact mode_anchor (ActualGroundProgram.coupling F) (Bulk.hinge F)
    (ActualGroundContraction.rayMap K F B)
    (vertex W.power (Bulk.markFn S F W) (Bulk.geometric K F w W) r)
    (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank
      (K.covariance F w) (K.symm F w)) (fun _ => 1) s

end YM.Integration.ActualAnchoredGround
end
