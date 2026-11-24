import YM.Integration.ActualGroundProgram
import YM.Integration.PatternConnectedProgram

/-!
# A fixed physical field and the original connected contraction

The one-dimensional external alphabet parametrizes exactly the chosen
original physical field. Its value one is that field and its value zero
is the original zero field. The Gaussian alphabet is still the full
original free-fine alphabet. No physical coordinate sum is introduced.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualGroundContraction

open Finset Function
open YM.RG YM.Precision YM.Lattice YM.Wilson YM.Exterior YM.Tree
open YM.Marker YM.Multi YM.Next.Rank YM.Next.SectorChange
open YM.Comparison.RG02 YM.Comparison.RG02.Order
open YM.Comparison.RG02.Cumulants YM.Comparison.RG02.Laplace
open YM.Extra.Trajectories (connected)
open YM.Integration.NormalizedKernelProgram (vertex)
open YM.Integration.PatternConnectedProgram
open scoped BigOperators ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip}
  {P : PathData G} {O : ChartRatio G}
variable (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (w : S.Choices)
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable (W : Bulk.Colors R G f) (r : ℕ)

def rayMap (B : fieldDir G c 1) :
    (Unit → ℝ) →ₗ[ℝ] Bulk.Joint S F (G := G) where
  toFun x := x () • (0, Bulk.classical S F (K.b F) B)
  map_add' x y := add_smul (x ()) (y ()) _
  map_smul' a x := mul_smul a (x ()) _

/-- The external coordinate is exactly one at the given original field. -/
theorem ray_stage (B : fieldDir G c 1) :
    Bulk.stage K F B =
      ActualGroundProgram.coupling F + rayMap K F B (fun _ => 1) := by
  change ((1 : ℝ), Bulk.classical S F (K.b F) B) =
    (1, 0) + (1 : ℝ) • (0, Bulk.classical S F (K.b F) B)
  rw [one_smul]
  exact Prod.ext (add_zero _).symm (zero_add _).symm

/-- The same fixed external direction, at coordinate zero, is the
original zero field. The direction is not chosen again. -/
theorem ray_zero_stage (B : fieldDir G c 1) :
    Bulk.stage K F 0 = ActualGroundProgram.coupling F + rayMap K F B 0 := by
  simp only [ActualGroundProgram.stage_split K F 0,
    ActualGroundProgram.coordinates_zero, map_zero]

def program (n : ℕ) (B : fieldDir G c 1) : ℂ :=
  (n.factorial : ℂ)⁻¹ *
    ∑ s ∈ shards (Board R r) (Join.pair R.quiet (pick r n)),
      modeContraction (ActualGroundProgram.coupling F) (Bulk.hinge F) (rayMap K F B)
        (vertex W.power (Bulk.markFn S F W) (Bulk.geometric K F w W) r)
        (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank
          (K.covariance F w) (K.symm F w)) (fun _ => 1) s

def centeredProgram (n : ℕ) (B : fieldDir G c 1) : ℂ :=
  (n.factorial : ℂ)⁻¹ *
    ∑ s ∈ shards (Board R r) (Join.pair R.quiet (pick r n)),
      centeredMode (ActualGroundProgram.coupling F) (Bulk.hinge F) (rayMap K F B)
        (vertex W.power (Bulk.markFn S F W) (Bulk.geometric K F w W) r)
        (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank
          (K.covariance F w) (K.symm F w)) (fun _ => 1) s

/-- Every original positive-order ground coefficient is the exact
finite program with its Gaussian configurations already contracted. -/
theorem ground_program {n : ℕ} (hn : 0 < n) (hnr : n ≤ r)
    (B : fieldDir G c 1) :
    Symmetry.Orbit.ground K F w W r n B = program K F w W r n B := by
  rw [ActualGroundProgram.ground_connected K F w W r hn hnr B]
  unfold program
  apply congrArg ((n.factorial : ℂ)⁻¹ * ·)
  unfold Bulk.Fk
  rw [ray_stage K F B]
  exact kernel_contraction (ActualGroundProgram.coupling F) (Bulk.hinge F)
    (rayMap K F B) W.power (Bulk.markFn S F W) (Bulk.geometric K F w W)
    (K.covariance F w) (K.symm F w) r (fun _ => 1)
    (Join.pair R.quiet (pick r n))

/-- Centering removes exactly the patterns with no physical slot.
The remaining contraction keeps the same original field direction,
all Gaussian indices, all program multiplicities and the outer 1/n!. -/
theorem ground_centered {n : ℕ} (hn : 0 < n) (hnr : n ≤ r)
    (B : fieldDir G c 1) :
    Symmetry.Orbit.ground K F w W r n B -
        Symmetry.Orbit.ground K F w W r n 0 =
      centeredProgram K F w W r n B := by
  rw [ActualGroundProgram.ground_connected K F w W r hn hnr B,
    ActualGroundProgram.ground_connected K F w W r hn hnr 0, ← mul_sub]
  unfold centeredProgram
  apply congrArg ((n.factorial : ℂ)⁻¹ * ·)
  unfold Bulk.Fk
  rw [ray_stage K F B, ray_zero_stage K F B]
  exact kernel_centered (ActualGroundProgram.coupling F) (Bulk.hinge F)
    (rayMap K F B) W.power (Bulk.markFn S F W) (Bulk.geometric K F w W)
    (K.covariance F w) (K.symm F w) r (fun _ => 1)
    (Join.pair R.quiet (pick r n))

end YM.Integration.ActualGroundContraction
end
