import YM.Integration.WilsonConditionalTaylorWheelAffine

/-! The winding noise/penalty has the same whole nonlinear Wilson kernel
as the independent finite course, also when the two books name different
legitimate choices for logarithmic branches. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelPenalty
open Function Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch PowerSeries
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Jets WilsonCoeffUV WilsonCoeffUV.Blue
open scoped Classical BigOperators Matrix
variable {G:Gauge} {c f:Side} (S:StepData c f) (F:Forest S.ratio)

theorem full (h:S.patch.Branches S.kernel G) (a:S.Choices):
    flash (sprig (jointPen G S) 2)=Reef.noisePin S a:=by
  rw [sprig_flash,WilsonConditionalTaylorWheelBare.germ]
  change Reef.noisePin (G:=G) S (tac S)=Reef.noisePin S a
  exact Reef.clash S h _ _

theorem original (h:S.patch.Branches S.kernel G) (a:S.Choices)
    (M:Matrix (Body 1 f) (Body 1 c) ℝ) (z:Active G F⊕Woods G c→ℝ) (e:ℕ):
    MvPolynomial.eval z (coeff e (loom (panSlice G S F (extractV G S F M)) (flash (sprig (jointPen G S) 2))))=
      MvPolynomial.eval (Sum.elim (Reef.offer G F ((leftArm z∘(Reef.pines F).symm)+Flat.rawMean G S F M*ᵥrightArm z))
        (rightArm z)) (coeff e (Reef.noisePin S a)):=by
  rw [full S h a]
  simp only [loom,PowerSeries.coeff_map]
  change MvPolynomial.eval z (cord (panSlice G S F (extractV G S F M)) (coeff e (Reef.noisePin S a)))=_
  rw [cord_apply,WilsonConditionalTaylorWheelAffine.joint]

end YM.Integration.WilsonConditionalTaylorWheelPenalty
end

