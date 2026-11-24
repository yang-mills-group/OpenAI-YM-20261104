import YM.Integration.WilsonCommonConditionalGaussian
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Gaussian

/-! The Gaussian and free Hessian of a finite moving conditional are
the same complete original Gaussian as in the independently normalized
formal marked step. No limiting covariance argument is needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingGaussianGeometry
open Function Matrix MeasureTheory
open Lattice RG Precision Push.Uniform Next.SectorChange Comparison.RG02 Wilson Tree Exterior
open Next.Free Bloch FreeResolvent WilsonCoeffUV
open FormalBulk08 Flat Reef PhysicalNext.Repeat.Legato
open scoped ContDiff

theorem law {I : Type} [Fintype I] [DecidableEq I] (Q : Matrix I I ℝ) :
    Further.GaussianScalar.fieldLaw Q = Gaussian.cloud Q := rfl

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (v : S.Choices)

/-- The free block used by the measured action, before any mark is
inserted or any output direction is chosen. -/
theorem covariance :
    (Push.Uniform.block (priced F v p P) 0)⁻¹ = K.covariance F v := by
  let X := Positions (Primary c G)
  let Y := Positions (Key F G)
  have zero : meetVar (0:X) (0:Y)=0 := (partSpace _ _).symm.map_zero
  have z := ((K.critical F).2.2 v).1
  have moved : ContDiffAt ℝ ω (priced F v p P) (0:Positions (Joint F G)) := by
    unfold priced
    apply ContDiffAt.comp _ _ (paint F G).contDiff.contDiffAt
    rwa [map_zero]
  have bought := Push.Uniform.block_congr F v (zero.symm ▸ moved)
  rw [zero,map_zero,map_zero] at bought
  exact congrArg (fun T => T⁻¹) bought

/-- Equality of the full probability laws on the same actual free
coordinates of the selected forest and tagged physical run. -/
theorem onRun (R : Run G) (N i per : ℕ) (hi : i<N)
    (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices) :
    let H := R.family.path.rep N per (i+1)
    Further.GaussianScalar.fieldLaw (Push.Uniform.block (priced F tag H.clip H.path) 0)⁻¹ =
      Gaussian.cloud ((Flat.testPrecision G (R.family.path.levels.clock.op i per) F
        (destination R.family.path.levels N i).wing).submatrix (Reef.pines F) (Reef.pines F))⁻¹ := by
  intro H
  let native := (RunFormalChain.fromRun R).step N i per hi
  rw [law,covariance native F tag,WilsonCommonConditionalGaussian.covariance R N i per hi F tag]

end YM.Integration.WilsonMovingGaussianGeometry
