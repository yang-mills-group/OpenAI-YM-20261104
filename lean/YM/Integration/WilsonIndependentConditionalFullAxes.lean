import YM.Integration.WilsonIndependentConditionalAffineLines
import YM.Integration.WilsonIndependentPublicFreeFields

/-! Gauge-fixed tree noise on the full ordinary fine link axes and the retained
coarse field. Only the planted variables fluctuate. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalFullAxes
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Convention RegulatorIR RegulatorIR.Diagram
open WilsonIndependentConditionalHeldGaussian WilsonIndependentConditionalAffineLines
open PertExtension PertExtension.GaussianScore MeasureTheory PowerSeries
open Lattice FreeResolvent Metric RG Wilson Tree Precision Matrix Exterior
open scoped Classical BigOperators MatrixOrder

variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)
   (H:FaceRow)(hf:(treeMatrix G S F H).PosDef)
def lifted : Joint G f c→Module.Dual ℝ (Lawn (Active G F)):=
  directions (overM G S F) (noise (tooth (X:=Active G F)))

theorem centered (b:Woods G c→ℝ):overM G S F*ᵥheld b=held b:=by
  classical
  ext i;cases i <;> simp [overM,bridgeM,held,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.one_apply]

theorem original :
    Gaussian.bond (law hf) (lifted (G:=G) S F)=fillSlots (Woods G c) (covariance G S F H):=by
  classical
  have inv:Gaussian.bond (law hf) (tooth (X:=Active G F))=(treeMatrix G S F H)⁻¹:=by
    have hc:treeMatrix G S F H*(treeMatrix G S F H)⁻¹=1:=Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hf.det_pos.ne')
    funext i j
    rw [Gaussian.bond_cross,Gaussian.bond,inverse_tooth hf hc]
  rw [lifted,lines,pad,inv]
  change bridgeM (reveal G S F) (Woods G c) * fillSlots (Woods G c) (treeMatrix G S F H)⁻¹ *
      (bridgeM (reveal G S F) (Woods G c)).transpose=fillSlots (Woods G c) (covariance G S F H)
  simp [bridgeM,fillSlots,Matrix.fromBlocks_multiply,Matrix.fromBlocks_transpose,covariance,reduce,
     treeInverse,resolve,reveal]

theorem hearing (μ:Measure (Lawn (Active G F)))(b:Woods G c→ℝ)(P:Ink (Joint G f c)):
   burn (law hf) (noise (tooth (X:=Active G F))) μ (loom (overM G S F) P) (held b)=
    burn (law hf) (lifted S F) μ P (held b):=by
  rw [WilsonIndependentConditionalAffineLines.hearing,centered]
  rfl

end YM.Integration.WilsonIndependentConditionalFullAxes
