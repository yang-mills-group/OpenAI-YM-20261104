import YM.Integration.OriginalMarkedHeatCovariance
import YM.Integration.MSFixedRatioGaussianGeometry
import YM.Integration.WilsonMarkedGaussianQuotient

/-! The independently prescribed squared form and affine response on the same
finite Wilson block. The covariance is identified in every free coordinate;
the deterministic copy in the marked chart is kept in the comparison of means. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCommonConditionalGaussian

open Function Lattice Laurent Wilson RG Precision Tree Exterior Matrix Bloch
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef Next.Free
open scoped Topology BigOperators Matrix Classical ContDiff

variable {G : Gauge} {c f : Side}

/-- The formal affine response and the independently derived response in
the free-link coordinates of the physical forest are the same linear map. -/
theorem coordinate (S : StepData c f) (F : Forest S.ratio)
    (W : Matrix (Body 1 f) (Body 1 c) ℝ) (x : fieldDir G c 1) (u : Precision.Key F G) :
    (Flat.rawMean G S F W *ᵥ FreeResolvent.flatten x) (Reef.pines F u) =
      (FreeResolvent.reduce G S F *ᵥ
        (FreeResolvent.tensor G (extracted S F W) *ᵥ FreeResolvent.flatten x)) u := by
  have h := congrArg (fun M => M *ᵥ FreeResolvent.flatten x) (Flat.unstitch G F W)
  rw [← Matrix.mulVec_mulVec,MSFixedRatioGaussianGeometry.color] at h
  have hi := congrFun h (Reef.pines F u).val
  rw [Flat.bring_alive F _ (Reef.pines F u)] at hi
  rw [FreeResolvent.reduce_actual]
  exact hi

variable (R : Run G) (N i per : ℕ) (hi : i<N)
    (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices)

/-- On this actual forest the original full covariance, including every
off-diagonal entry, is the inverse of the actual independent formal quadratic
form. The face field on the incoming mesh is fixed by the original run. -/
theorem covariance :
    ((RunFormalChain.fromRun R).step N i per hi).covariance F tag =
      ((Flat.testPrecision G (R.family.path.levels.clock.op i per) F
        (destination R.family.path.levels N i).wing).submatrix (Reef.pines F) (Reef.pines F))⁻¹ := by
  have h := MSFixedRatioGaussianGeometry.restricted (G:=G) (R.family.path.levels.clock.op i per)
    F (destination R.family.path.levels N i).wing (freeForms R.family.path.levels N (i+1)) rfl
  rw [show (Flat.testPrecision G (R.family.path.levels.clock.op i per) F
    (destination R.family.path.levels N i).wing).submatrix (Reef.pines F) (Reef.pines F) = _ from h]
  rw [OriginalMarkedHeatCovariance.activeCovariance R N i per hi F tag]
  simp only [FreeResolvent.treeInverse,FreeResolvent.resolve,zero_smul,add_zero]

include tag in
/-- Restoring the affine copy gives the exact same original conditional
mean as the formal Gaussian prescription, on every coarse direction and every
free fine coordinate. The centered chart alone has the displayed subtraction. -/
theorem mean (x : fieldDir G (R.family.S.side i per) 1) :
    FreeResolvent.active F (fderiv ℝ (((RunFormalChain.fromRun R).step N i per hi).b F) 0 x) +
      OriginalMarkedHeatCovariance.copyCharge R i per F x =
    fun u => (Flat.rawMean G (R.family.path.levels.clock.op i per) F
        (Bloch.installed (R.family.path.levels.clock.op i per).ratio
          ((destination R.family.path.levels N i).duo R.family.path.levels.clock.kernel.penalty).A0) *ᵥ
          FreeResolvent.flatten x) (Reef.pines F u) := by
  rw [OriginalMarkedHeatCovariance.stationary R N i per hi F tag x,sub_add_cancel]
  funext u
  exact (coordinate (R.family.path.levels.clock.op i per) F _ x u).symm

end YM.Integration.WilsonCommonConditionalGaussian

