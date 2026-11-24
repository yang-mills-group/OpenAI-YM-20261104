import YM.Integration.WilsonIndependentConditionalMerShift
import YM.Integration.WilsonIndependentConditionalMarkedCover

/-! All filed Mer tensors are obtained from the unshifted, fully heated word
by the actual finite affine predictor. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalMerSlates
open Function Matrix Lattice RG WilsonCoeffUV Laurent Bloch Metric WilsonCoeffUV.Blue
open FreeResolvent Work.F08 WilsonCoeffUV.Bank Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil Precision Embroider RegulatorIR RegulatorIR.Diagram PowerSeries
open scoped BigOperators Classical
variable {G:Gauge}{c f:Side}(S:StepData c f)(Ñ:ChartRatio G)
variable (B:Matrix (Woods G f) (Woods G f) ℝ)

def slate (M:Matrix (Woods G f) (Woods G c) ℝ)(P w:PChart G f)(k:ℕ)(i:ℕ):Gen ℝ (Joint G f c):=
  let L:=fillSlots (Woods G c) B
  ∑ j∈Finset.range (1+k+3*i),bul L (abr L (casePW S Ñ M P)) (srCold w M) j i

theorem shell {P w:PChart G f}{k:ℕ}(p:shellK 2 P)(r:LocalRatio Ñ)(h:shellK k w)(M):
    shellK k (slate S Ñ B M P w k):=by
  let L:=fillSlots (Woods G c) B
  have bound:=stops_bul L (span_abr L (pack_band S (M:=M) p) (pack_zero S r)) k (fade_shell (camber G M) h)
  intro e j hj
  unfold slate
  rw [Finset.sum_apply,Finset.sum_eq_zero]
  intro i _
  apply bound
  exact Or.inl hj

theorem pure {P w:PChart G f}{k:ℕ}(h:∀i,Pure (w i))(M)(e):
    Pure (slate S Ñ B M P w k e):=pure_sum fun j _=>pure_bul _ _ (fun i=>fade_pure (h i) _) j e

theorem printed {P w:PChart G f}{k:ℕ}(p:shellK 2 P)(r:LocalRatio Ñ)(h:shellK k w)(M):
    WilsonIndependentConditionalMerShift.carried (fillSlots (Woods G c) B) (casePW S Ñ M P) (srCold w M) k=
      flash (slate S Ñ B M P w k):=by
  apply at_one
  exact stops_bul _ (span_abr _ (pack_band S p) (pack_zero S r)) k (fade_shell (camber G M) h)

theorem moved {P w:PChart G f}{k:ℕ}(p:shellK 2 P)(r:LocalRatio Ñ)(h:shellK k w)
    (hp:∀i,Pure (P i))(hw:∀i,Pure (w i))(b:S.patch.Branches S.kernel G)
    (adj:B.transpose=B)(M:Matrix (Woods G f) (Woods G c) ℝ)(e):
    fade (groundM G M) (slate S Ñ B 0 P w k e)=slate S Ñ B M P w k e:=by
  have shifted:=WilsonIndependentConditionalMerShift.original S Ñ B adj M p r b h hp hw
  rw [printed S Ñ B p r h 0,printed S Ñ B p r h M,loom_fade _ _ (finite_shell (shell S Ñ B p r h 0))] at shifted
  funext s
  have row:=congrArg (fun x=>WilsonIndependentConditionalMarkedCover.tensor x e s) shifted
  exact (WilsonIndependentConditionalMarkedCover.reads (fade_shell _ (shell S Ñ B p r h 0))
    (fun i=>fade_pure (pure S Ñ B hw 0 i) _) e s).symm.trans (row.trans
      (WilsonIndependentConditionalMarkedCover.reads (shell S Ñ B p r h M) (pure S Ñ B hw M) e s))

theorem original (T:Forest S.ratio)(H:FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)
    {P w:PChart G f}{k:ℕ}(p:shellK 2 P)(r:LocalRatio Ñ)(h:shellK k w)
    (hp:∀i,Pure (P i))(hw:∀i,Pure (w i))(b:S.patch.Branches S.kernel G)
    (adj:(covariance G S T H).transpose=covariance G S T H)(i:ℕ):
    reed S T H Q Ñ P k w i=fade plug
      (fade (groundM G (extractV G S T Q)) (slate S Ñ (covariance G S T H) 0 P w k i)):=by
  rw [moved S Ñ _ p r h hp hw b adj]
  rfl

end YM.Integration.WilsonIndependentConditionalMerSlates
