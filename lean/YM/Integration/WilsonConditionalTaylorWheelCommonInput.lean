import YM.Integration.WilsonConditionalTaylorWheelReef
import YM.Integration.WilsonMovingFiniteConditional

/-! Both original constructions use the identical full finite Gaussian
integrand on every physical scalar field and every retained source term. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelCommonInput
open Function Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch PowerSeries
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Jets FormalBulk08.Orb
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonConditionalTaylorWheelHaar
open scoped Classical BigOperators Matrix
variable {G:Gauge} {c f:Side} (S:StepData c f) (F:Forest S.ratio)

def point (M:Matrix (Body 1 f) (Body 1 c) ℝ) (z:Active G F⊕Woods G c→ℝ):
    Pine G S F⊕wire G c→ℝ:=Sum.elim (drift (G:=G) S F M z) (rightArm z)

theorem signed (O:ChartRatio G) (law:LocalRatio O) (P:PChart G f) (degree:shellK 2 P)
    (branches:S.patch.Branches S.kernel G) (a:S.Choices) (M:Matrix (Body 1 f) (Body 1 c) ℝ)
    (z: Active G F⊕Woods G c→ℝ) (e:ℕ):
    MvPolynomial.eval z (coeff e (shot S F M O P))=
      MvPolynomial.eval (point (G:=G) S F M z) (coeff e
        (WilsonMovingFiniteConditional.interaction (Reef.flush F a O (-flash P)))):=by
  by_cases zero:e=0
  · subst e
    have h:coeff 0 (shot S F M O P)=0:=by
      rw [shot,loom,coeff_map,coeff_zero_eq_constantCoeff_apply,flash_blank (pack_zero S law),map_zero]
    rw [h,WilsonMovingFiniteConditional.interaction,map_sub,coeff_zero_C,sub_self,map_zero,map_zero]
  · have pos:0<e:=Nat.pos_of_ne_zero zero
    rw [WilsonConditionalTaylorWheelShot.original S F O law P degree branches a M z e pos,
      WilsonConditionalTaylorWheelReef.haar S F O law M z e,WilsonMovingFiniteConditional.interaction,
      map_sub,coeff_C,if_neg zero,sub_zero,point,WilsonConditionalTaylorWheelReef.primitive S F O law,
      map_neg,map_neg]
    ring

theorem marked (M:Matrix (Body 1 f) (Body 1 c) ℝ) (T:Pap (wire G f))
    (z:Active G F⊕Woods G c→ℝ) (e:ℕ):
    MvPolynomial.eval z (coeff e (loom (camSlice G S F (extractV G S F M)) T))=
      MvPolynomial.eval (point (G:=G) S F M z) (coeff e (Reef.seat F T)):=by
  have h:=congrArg (coeff e) (WilsonMovingForestRestriction.seat F (point (G:=G) S F M z) T)
  rw [glimpse_coeff,glimpse_coeff] at h
  rw [loom,PowerSeries.coeff_map]
  change MvPolynomial.eval z (cord _ _)=_
  rw [cord_apply,WilsonConditionalTaylorWheelAffine.fine S F M z]
  exact h.symm

end YM.Integration.WilsonConditionalTaylorWheelCommonInput
end

