import YM.Integration.NormalizedKernelProgram
import YM.Comparison.RG02.Symmetry.Code

/-!
# Original ground coefficients as finite ordered tensor programs

This is an algebraic application to the original Bulk.geometric
function, not to a substituted vacuum or linearized geometry. The
physical coordinate map is the original gaugeCount on coarse links;
the Gaussian map remains the original hinge on free fine links. Their
index types are distinct.

The positive-order ground coefficient retains its outer 1/n! and the
full normalized vacuum logarithm. Only the explicitly displayed
difference at physical field zero removes assignments having no
physical external slot.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualGroundProgram

open Finset Function
open YM.RG YM.Precision YM.Lattice YM.Wilson YM.Exterior YM.Tree
open YM.Marker YM.Multi YM.Next.Rank YM.Next.SectorChange
open YM.Comparison.RG02 YM.Comparison.RG02.Order
open YM.Comparison.RG02.Cumulants YM.Comparison.RG02.Laplace
open YM.Extra.Trajectories (connected)
open YM.Integration.FiniteConnectedProgram YM.Integration.NormalizedKernelProgram
open scoped BigOperators ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip}
  {P : PathData G} {O : ChartRatio G}
variable (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (w : S.Choices)
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable (W : Bulk.Colors R G f) (r : ℕ)

abbrev PhysicalIndex (G : Gauge) (c : Side) := Body 1 c × G.ColorIndex

def coordinates (B : fieldDir G c 1) : PhysicalIndex G c → ℝ :=
  (gaugeCount (G := G) (ι := Body 1 c)).symm B

def coupling : Bulk.Joint S F (G := G) := (1, 0)

def physicalMap : (PhysicalIndex G c → ℝ) →ₗ[ℝ] Bulk.Joint S F (G := G) :=
  let C : (PhysicalIndex G c → ℝ) ≃L[ℝ] fieldDir G c 1 :=
    gaugeCount (G := G) (ι := Body 1 c)
  let D : fieldDir G c 1 →L[ℝ] Bulk.SliceDir S F G :=
    (ContinuousLinearMap.id ℝ _).prod (fderiv ℝ (K.b F) 0)
  ((ContinuousLinearMap.inr ℝ ℝ _).comp (D.comp C.toContinuousLinearMap)).toLinearMap

theorem coordinates_zero : coordinates (0 : fieldDir G c 1) = 0 :=
  map_zero _

/-- Exact original affine frame, with coupling coordinate one and the
unchanged derivative of the original stationary map. -/
theorem stage_split (B : fieldDir G c 1) :
    Bulk.stage K F B = coupling F + physicalMap K F (coordinates B) := by
  let C : (PhysicalIndex G c → ℝ) ≃L[ℝ] fieldDir G c 1 :=
    gaugeCount (G := G) (ι := Body 1 c)
  have hC : C (coordinates B) = B := C.apply_symm_apply B
  change (1, Bulk.classical S F (K.b F) B) =
    (1, 0) + (0, (C (coordinates B), fderiv ℝ (K.b F) 0 (C (coordinates B))))
  rw [hC]
  exact Prod.ext (add_zero _).symm (zero_add _).symm

def originalRows (B : fieldDir G c 1) :
    Hot (Board R r) → Rows (Precision.Key F G) :=
  kernelRows (coupling F) (Bulk.hinge F) (physicalMap K F)
    W.power (Bulk.markFn S F W) (Bulk.geometric K F w W) r (coordinates B)

def program (n : ℕ) (B : fieldDir G c 1) : ℂ :=
  (n.factorial : ℂ)⁻¹ *
    ∑ s ∈ shards (Board R r) (Join.pair R.quiet (pick r n)),
      modeValue
        (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank
          (K.covariance F w) (K.symm F w))
        (originalRows K F w W r B) s

def centeredProgram (n : ℕ) (B : fieldDir G c 1) : ℂ :=
  (n.factorial : ℂ)⁻¹ *
    ∑ s ∈ shards (Board R r) (Join.pair R.quiet (pick r n)),
      centeredMode (coupling F) (Bulk.hinge F) (physicalMap K F)
        (vertex W.power (Bulk.markFn S F W) (Bulk.geometric K F w W) r)
        (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank
          (K.covariance F w) (K.symm F w)) (coordinates B) s

/-- Positive order removes only the separately defined classical
order-zero price; the complete vacuum logarithm remains. -/
theorem ground_connected {n : ℕ} (hn : 0 < n) (hnr : n ≤ r)
    (B : fieldDir G c 1) :
    Symmetry.Orbit.ground K F w W r n B =
      (n.factorial : ℂ)⁻¹ *
        (connected (Bulk.Fk K F w W B r)).part
          (Join.pair R.quiet (pick r n)) := by
  rw [Symmetry.Orbit.ground, if_neg (ne_of_gt hn), add_zero,
    detail, observe, if_pos hnr]
  change (n.factorial : ℂ)⁻¹ *
    (logVac (Bulk.Fk K F w W B r)).part (Join.pair R.quiet (pick r n)) = _
  rw [Valence.log_v_part _ (Bulk.fk_unit K F w W B r),
    Join.left_pair, if_pos rfl]

/-- Full exact original-field coefficient: all normalized ordered
vertices, all Cloud compositions, and every pairing program entry. -/
theorem ground_program {n : ℕ} (hn : 0 < n) (hnr : n ≤ r)
    (B : fieldDir G c 1) :
    Symmetry.Orbit.ground K F w W r n B = program K F w W r n B := by
  rw [ground_connected K F w W r hn hnr B]
  unfold program
  apply congrArg ((n.factorial : ℂ)⁻¹ * ·)
  unfold Bulk.Fk
  rw [stage_split K F B]
  exact kernel_program (coupling F) (Bulk.hinge F) (physicalMap K F)
    W.power (Bulk.markFn S F W) (Bulk.geometric K F w W)
    (K.covariance F w) (K.symm F w) r (coordinates B)
    (Join.pair R.quiet (pick r n))

/-- Centering the original ground coefficient retains precisely the
full connected programs with at least one physical external slot. -/
theorem ground_centered {n : ℕ} (hn : 0 < n) (hnr : n ≤ r)
    (B : fieldDir G c 1) :
    Symmetry.Orbit.ground K F w W r n B -
        Symmetry.Orbit.ground K F w W r n 0 =
      centeredProgram K F w W r n B := by
  rw [ground_program K F w W r hn hnr B,
    ground_program K F w W r hn hnr 0]
  unfold program originalRows centeredProgram
  rw [coordinates_zero, ← mul_sub, ← Finset.sum_sub_distrib]
  apply congrArg ((n.factorial : ℂ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro s _
  exact mode_centered (coupling F) (Bulk.hinge F) (physicalMap K F)
    (vertex W.power (Bulk.markFn S F W) (Bulk.geometric K F w W) r)
    (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank
      (K.covariance F w) (K.symm F w)) (coordinates B) s

end YM.Integration.ActualGroundProgram
end
