import YM.Integration.WilsonConditionalTaylorWheelKernel
import YM.Integration.WilsonMovingRunWickCoordinates

/-! Equality on *all fine links*, not just the free forest subset, of the
winding stationary affine chart and the independently derived chart. Both
the external coarse copy and the full nonzero classical mean are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelAffine
open Function Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef WilsonCoeffUV WilsonCoeffUV.Blue
open scoped Classical BigOperators Matrix
variable {G:Gauge} {c f:Side} (S:StepData c f) (F:Forest S.ratio)

private theorem same (i:Woods G f) (a:Active G F):
    reveal G S F i a=(dropRoot G S F).transpose i (Reef.pines F a):=by
  change (if plant F a=i then 1 else 0)=(1:Matrix (Woods G f) _ ℝ) (Reef.pines F a).val i
  rw [Matrix.one_apply]
  rfl

theorem injection (x:Active G F→ℝ):
    reveal G S F*ᵥx=Reef.offer G F (x∘(Reef.pines F).symm):=by
  funext i
  change ∑k,reveal G S F i k*x k=∑k,(dropRoot G S F).transpose i k*x ((Reef.pines F).symm k)
  rw [←(Reef.pines F (G:=G)).sum_comp (fun k=>(dropRoot G S F).transpose i k*x ((Reef.pines F).symm k))]
  simp only [Equiv.symm_apply_apply,same]

theorem stationary (M:Matrix (Body 1 f) (Body 1 c) ℝ) (x:Woods G c→ℝ):
    extractV G S F M*ᵥx=Reef.offer G F (Flat.rawMean G S F M*ᵥx):=by
  change tensor G (extracted S F M)*ᵥx=(dropRoot G S F).transpose*ᵥ (Flat.rawMean G S F M*ᵥx)
  rw [Matrix.mulVec_mulVec,Flat.unstitch,MSFixedRatioGaussianGeometry.color]

theorem fine (M:Matrix (Body 1 f) (Body 1 c) ℝ) (z:Active G F⊕Woods G c→ℝ):
    camSlice G S F (extractV G S F M)*ᵥz=
      Reef.offer G F ((leftArm z∘(Reef.pines F).symm)+Flat.rawMean G S F M*ᵥrightArm z):=by
  rw [camber_tree,Matrix.add_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,
    left_hit,right_hit,injection,stationary,map_add]

theorem joint (M:Matrix (Body 1 f) (Body 1 c) ℝ) (z:Active G F⊕Woods G c→ℝ):
    panSlice G S F (extractV G S F M)*ᵥz=
      Sum.elim (Reef.offer G F ((leftArm z∘(Reef.pines F).symm)+Flat.rawMean G S F M*ᵥrightArm z)) (rightArm z):=by
  rw [arm_pan,fine]
end YM.Integration.WilsonConditionalTaylorWheelAffine
end

