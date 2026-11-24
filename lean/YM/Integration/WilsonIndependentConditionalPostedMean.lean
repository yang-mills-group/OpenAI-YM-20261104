import YM.Integration.WilsonIndependentConditionalOrdinaryBoard

/-! The affine predictor acts only on held links.  On the genuine original
fine-tree noise this gives an equality of the complete tilted integrals
before or after substituting the conditional mean. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalPostedMean
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Convention RegulatorIR RegulatorIR.Diagram
open WilsonIndependentConditionalHeldGaussian WilsonIndependentConditionalAffineLines WilsonIndependentConditionalFullAxes
open PertExtension PertExtension.GaussianScore MeasureTheory PowerSeries Matrix
open Lattice FreeResolvent Metric RG Wilson Tree Precision
open scoped Classical BigOperators MatrixOrder
variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)

theorem inlet (a:Woods G c):lifted (G:=G) S F (.inr a)=0:=by
  classical
  simp [WilsonIndependentConditionalFullAxes.lifted,directions,overM,bridgeM,noise,Fintype.sum_sum_type]

theorem directions_fixed (M:Matrix (Woods G f) (Woods G c) ℝ):
    directions (groundM G M) (lifted (G:=G) S F)=lifted S F:=by
  classical
  funext j
  cases j with
  | inl j=>
    simp [directions,groundM,Fintype.sum_sum_type,inlet (G:=G) S F,Matrix.one_apply]
  | inr j=>
    simp [directions,groundM,Fintype.sum_sum_type,inlet (G:=G) S F,Matrix.one_apply]

theorem shifted (M:Matrix (Woods G f) (Woods G c) ℝ)(b:Woods G c→ℝ):
    groundM G M *ᵥ held b=Sum.elim (M*ᵥb) b:=by
  rw [groundM,Matrix.fromBlocks_mulVec]
  ext j;cases j <;> simp [held]

theorem hearing {H:FaceRow}(hf:(treeMatrix G S F H).PosDef)(μ:Measure (Lawn (Active G F)))
    (M:Matrix (Woods G f) (Woods G c) ℝ)(b:Woods G c→ℝ)(P:Ink (Joint G f c)):
    burn (law hf) (lifted S F) μ (loom (groundM G M) P) (held b)=
      burn (law hf) (lifted S F) μ P (Sum.elim (M*ᵥ b) b):=by
  rw [WilsonIndependentConditionalAffineLines.hearing,directions_fixed,shifted]

private theorem zeroM:groundM G (0:Matrix (Woods G f) (Woods G c) ℝ)=1:=by
  classical
  ext j i;cases j <;> cases i <;> simp [groundM,Matrix.one_apply]

private theorem first (M:Matrix (Woods G f) (Woods G c) ℝ):
    camber G (0:Matrix (Woods G f) (Woods G c) ℝ)*groundM G M=camber G M:=by
  simpa [camber] using (arm_ground G M).1

theorem vacuum (Ñ:ChartRatio G)(M:Matrix (Woods G f) (Woods G c) ℝ){P:PChart G f}(p:shellK 2 P):
    loom (groundM G M) (flash (casePW S Ñ 0 P))=flash (casePW S Ñ M P):=by
  rw [sterol S p Ñ 0,sterol S p Ñ M,map_sub,map_sub]
  have compose {I J U:Type}[Fintype I][Fintype J][Fintype U]
      (A:Matrix I J ℝ)(B:Matrix J U ℝ)(H:Ink I):
      loom B (loom A H)=loom (A*B) H:=DFunLike.congr_fun (loom_loom A B) H
  rw [compose,compose,compose,first,zeroM,Matrix.one_mul]

set_option maxHeartbeats 2000000 in
theorem mark (M:Matrix (Woods G f) (Woods G c) ℝ){w:PChart G f}{k:ℕ}(h:shellK k w):
    loom (groundM G M) (flash (srCold w (0:Matrix (Woods G f) (Woods G c) ℝ)))=flash (srCold w M):=by
  have atM (J:Matrix (Woods G f) (Woods G c) ℝ):
    loom (camber G J) (flash w)=flash (srCold w J):=loom_fade _ w (finite_shell h)
  let Z:Matrix (Woods G f) (Woods G c) ℝ:=0
  calc
    _=loom (groundM G M) (loom (camber G Z) (flash w)):=congrArg _ (atM Z).symm
    _=loom (camber G Z*groundM G M) (flash w):=DFunLike.congr_fun (loom_loom (camber G Z) (groundM G M)) (flash w)
    _=loom (camber G M) (flash w):=by rw [show camber G Z*groundM G M=camber G M from first M]
    _=flash (srCold w M):=atM M

end YM.Integration.WilsonIndependentConditionalPostedMean
