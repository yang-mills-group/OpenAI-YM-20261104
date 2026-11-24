import YM.Integration.WilsonIndependentSpoutAmbientLog
import YM.Integration.WilsonIndependentSpoutPostedSchool

/-! The true nonlinear unmarked next age on its finite measured board. The
complete held logarithm is taken before its field-independent part is removed. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutTrueFiniteVacuum
open Function PowerSeries Matrix Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open RegulatorIR RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Halo RegulatorIR.Diagram RegulatorIR.Oracle RegulatorIR.Ledger
open RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Calibration
open PertExtension Tree FreeResolvent Metric Precision Exterior Wilson WilsonCoeffUV.Power
open WilsonIndependentConditionalPositiveVacuum (value)
open WilsonIndependentSpoutUnshiftedPost (bank)
open scoped Classical BigOperators Matrix

variable {G:Gauge}{c l:Side}
theorem covariance (S:StepData c l)(F:Forest S.ratio)(H:FaceRow)(M:Matrix (Woods G l) (Woods G c) ℝ):
    panSlice G S F M*fillSlots (Woods G c) (treeInverse G S F H 0)*(panSlice G S F M).transpose=
      fillSlots (Woods G c) (FreeResolvent.covariance G S F H):=by
  let X:=fillSlots (Woods G c) (treeInverse G S F H 0)
  have basis:overM G S F*X*(overM G S F).transpose=fillSlots (Woods G c) (FreeResolvent.covariance G S F H):=by
    simp [X,overM,bridgeM,fillSlots,Matrix.fromBlocks_multiply,Matrix.fromBlocks_transpose,
      FreeResolvent.covariance,reduce,treeInverse,FreeResolvent.resolve,reveal]
  rw [panSlice,Matrix.transpose_mul]
  change (groundM G M*overM G S F)*X*((overM G S F).transpose*(groundM G M).transpose)=_
  rw [show (groundM G M*overM G S F)*X*((overM G S F).transpose*(groundM G M).transpose)=
    groundM G M*(overM G S F*X*(overM G S F).transpose)*(groundM G M).transpose from by simp only [Matrix.mul_assoc],
    basis,WilsonIndependentConditionalMerShift.fixed]

variable {W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)(A:Levels G)(s:ℕ)

theorem original (simple:G.Simple)(p:ℕ)(n:Side)
    (paid:WilsonIndependentSpoutMeasuredHearing.Hearing C Z D f A s p n):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let P:=loose A m
    let S:=mStep A n m;let F:=repeatF S;let H:=freeForms A N (m+1);let H':=freeForms A N m
    let Ñ:=XSpace.Bare.chart G;let b:=n*P.L;let V:=(story A Ñ N (m+1)).1 b
    let α:=tale (D f.prev).dine;let β:=relativeC A Ñ N m (N-m)
    let T:=bank P n (C.bore G Z (sheet D) f) α V;let U:=panSlice G S F (extractV G S F (roam A N m n))
    let E:=WilsonIndependentConditionalRawVacuum.finite (fillSlots (Woods G n) (FreeResolvent.covariance G S F H)) T
    logOf (Wick (Woods G n) (treeInverse G S F H 0) (raiseE (loom U (Blue.flash T))))=
       projectZero (loom U (Blue.flash E)) ∧
    ∀e≤p,∀y:TreeVars G n,value (projectZero (loom U (Blue.flash E))) e y=
      value (orbC (precisionC G n H')) e y-value (redo β (Blue.flash ((story A Ñ N m).1 n))) e y:=by
  intro N m P S F H H' Ñ b V α β T U E
  have age:m<N:=by dsimp only [N,m];have:=f.ok;omega
  have basis:Interlace H V:=(old A Ñ simple (XSpace.Bare.chart_ratio G) N (m+1) age).basis b
  have actual:=WilsonIndependentSpoutPostedSchool.original C Z D f P n α V basis.lamp basis.shape
  dsimp only at actual
  have adj:(treeInverse G S F H 0).transpose=treeInverse G S F H 0:=by
    unfold treeInverse FreeResolvent.resolve
    rw [zero_smul,add_zero,transpose_nonsing_inv,treeMatrix,transpose_submatrix,full_symmetric _ (age_sym A N (m+1) b)]
  have answer:=WilsonIndependentSpoutAmbientLog.projected U _ adj actual.2.1 actual.1 actual.2.2
  rw [show U*fillSlots (Woods G n) (treeInverse G S F H 0)*U.transpose=fillSlots (Woods G n) (FreeResolvent.covariance G S F H) from
    covariance S F H _] at answer
  refine ⟨answer,?_⟩
  rw [←answer,WilsonIndependentSpoutPostedBank.landed C Z D f A N m n α V basis.lamp]
  exact paid.1

end YM.Integration.WilsonIndependentSpoutTrueFiniteVacuum
