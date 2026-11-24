import YM.Integration.WilsonConditionalTaylorWheelHaar
import YM.Integration.WilsonConditionalTaylorWheelPenalty

/-! Every positive coupling coefficient of the complete actual incoming
winding action, before the Gaussian. The terms are exactly the genuine
Wilson/Haar density, the independent nonlinear block penalty, and the
entire earlier angular energy, all at the same shifted real field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelShot
open Function Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch PowerSeries
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Jets WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonConditionalTaylorWheelAffine WilsonConditionalTaylorWheelHaar
open scoped Classical BigOperators Matrix
variable {G:Gauge} {c f:Side} (S:StepData c f) (F:Forest S.ratio)

private theorem scrubbed {U V:Type} [Fintype U] [Fintype V] (L:Matrix U V ℝ) (P:Pal ℝ U) (e:ℕ) (pos:0<e):
    coeff e (loom L (flash (scrub P)))=coeff e (loom L (flash P)):=by
  simp only [loom,PowerSeries.coeff_map,flash,coeff_mk,scrub,if_neg pos.ne']

theorem row (O:ChartRatio G) (P:PChart G f) (degree:shellK 2 P) (M:Matrix (Body 1 f) (Body 1 c) ℝ):
    let A:=extractV G S F M
    shot S F M O P=
      loom (camSlice G S F A) (Blue.jet (unhaar O))-
      loom (panSlice G S F A) (flash (scrub (sprig (jointPen G S) 2)))-
      loom (camSlice G S F A) (flash (scrub P)):=by
  intro A
  unfold shot
  rw [sterol S degree O,map_sub,map_sub]
  have remap (K:Matrix (Joint G f c) (Joint G f c) ℝ) (W:Blue.Ink (Joint G f c)):
      loom (overM G S F) (loom K W)=loom (K*overM G S F) W:=
    DFunLike.congr_fun (loom_loom K (overM G S F)) W
  have pre (K:Matrix (Woods G f) (Joint G f c) ℝ) (W:Blue.Ink (Woods G f)):
      loom (overM G S F) (loom K W)=loom (K*overM G S F) W:=
    DFunLike.congr_fun (loom_loom K (overM G S F)) W
  rw [pre,remap,pre];rfl

theorem original (O:ChartRatio G) (law:LocalRatio O) (P:PChart G f) (degree:shellK 2 P)
    (branches:S.patch.Branches S.kernel G) (a:S.Choices) (M:Matrix (Body 1 f) (Body 1 c) ℝ)
    (z:Active G F⊕Woods G c→ℝ) (e:ℕ) (pos:0<e):
    let y:=drift (G:=G) S F M z
    MvPolynomial.eval z (coeff e (shot S F M O P))=
      MvPolynomial.eval z (coeff e (Jets.paste (fun v=>Real.log (Reef.sap F O (drift (G:=G) S F M v)))))-
      MvPolynomial.eval (Sum.elim (Reef.offer G F y) (rightArm z)) (coeff e (Reef.noisePin S a))-
      MvPolynomial.eval (Reef.offer G F y) (coeff e (flash P)):=by
  intro y
  rw [row S F O P degree M,map_sub,map_sub,map_sub,map_sub,scrubbed _ _ e pos,scrubbed _ _ e pos,
    WilsonConditionalTaylorWheelHaar.original S F O law M,WilsonConditionalTaylorWheelPenalty.original S F branches a M z e]
  congr 1
  change MvPolynomial.eval z (cord (camSlice G S F (extractV G S F M)) (coeff e (flash P)))=_
  rw [cord_apply,fine];rfl
end YM.Integration.WilsonConditionalTaylorWheelShot
end

