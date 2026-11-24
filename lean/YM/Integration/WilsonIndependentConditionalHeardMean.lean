import YM.Integration.WilsonIndependentConditionalPostedMean

/-! The normalized complete original Wilson transfer tested at the genuine
conditional mean after the unshifted finite-temperature operation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalHeardMean
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Convention RegulatorIR RegulatorIR.Diagram
open WilsonIndependentConditionalHeldGaussian WilsonIndependentConditionalDiagramResponse
open WilsonIndependentConditionalNotebookFilm Exterior
open PertExtension PertExtension.GaussianScore MeasureTheory PowerSeries Matrix
open Lattice FreeResolvent Metric RG Wilson Tree Precision
open scoped Classical BigOperators MatrixOrder
variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)(H:FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)

def unshifted (Ñ:ChartRatio G)(P w:PChart G f)(k:ℕ):Ink (Joint G f c):=
  let L:=fillSlots (Woods G c) (covariance G S F H)
  rated (fun e=>e+k) (endHeat k L (logHeat L (casePW S Ñ 0 P) false) (srCold w 0))

theorem original {Ñ:ChartRatio G}{P w:PChart G f}{k:ℕ}(hp:shellK 2 P)(ratio:LocalRatio Ñ)
    (wp:shellK (k+1) w)(branch:S.patch.Branches S.kernel G)(sym:(H.acts f).transpose=H.acts f)
    (pure:∀ i,Pure (P i))(wpure:∀ i,Pure (w i))(hf:(treeMatrix G S F H).PosDef)(b:Woods G c→ℝ):
    let M:=extractV G S F Q
    PowerSeries.map (emphasis (Sum.elim (M*ᵥ b) b)).toRingHom (unshifted S F H Ñ P w (k+1))=
      PowerSeries.map (emphasis b).toRingHom (flash (reed S F H Q Ñ P (k+1) w)):=by
  intro M
  let V:=casePW S Ñ (0:Matrix (Woods G f) (Woods G c) ℝ) P
  let W:=srCold w (0:Matrix (Woods G f) (Woods G c) ℝ)
  let V':=casePW S Ñ M P
  let d:=WilsonIndependentConditionalFullAxes.lifted (G:=G) S F
  let chart:=overM G S F
  let L:=fillSlots (Woods G c) (covariance G S F H)
  let X:=Sum.elim (M*ᵥb) b
  have vs:shellK 2 V:=pack_band S hp
  have zero:V 0=0:=pack_zero S ratio
  have ws:shellK (k+1) W:=fade_shell _ wp
  have pre (E:Ink (Joint G f c)):WilsonIndependentConditionalInsertion.read hf volume b
      (loom chart (loom (groundM G M) E))=burn (law hf) d volume E X:=by
    unfold WilsonIndependentConditionalInsertion.read
    rw [WilsonIndependentConditionalFullAxes.hearing,WilsonIndependentConditionalPostedMean.hearing]
  have expo {I J:Type}[Fintype I][Fintype J](A:Matrix I J ℝ)(E:Ink I):
      loom A (Formal.expo E)=Formal.expo (loom A E):=Formal.map_exp (cord A) _
  have formv:loom chart (loom (groundM G M) (Formal.expo (rated (fun e=>e+2) V)))=raiseE (shot S F Q Ñ P):=by
    rw [film vs,expo,WilsonIndependentConditionalPostedMean.vacuum S Ñ M hp,expo]
    change Formal.expo (PowerSeries.map (cord chart).toRingHom (flash V'))=raiseE _
    apply exponential
    rw [←coeff_zero_eq_constantCoeff_apply,coeff_map,flash,coeff_mk,
      show V' 0=0 from pack_zero S ratio];simp [totalR]
  have formw:loom chart (loom (groundM G M) (rated (fun e=>e+(k+1)) W))=loom (camSlice G S F M) (flash w):=by
    rw [film ws,WilsonIndependentConditionalPostedMean.mark M wp,show flash (srCold w M)=loom (camber G M) (flash w)
          from (loom_fade _ w (finite_shell wp)).symm]
    exact DFunLike.congr_fun (loom_loom (camber G M) chart) (flash w)
  have eqn:=green (law hf) d volume k V W X (vacuum vs zero) (pack_pure S ratio branch pure)
          (within ws) (fun i=>fade_pure (wpure i) _)
  rw [show Gaussian.bond (law hf) d=L from WilsonIndependentConditionalFullAxes.original S F H hf] at eqn
  have conv:=WilsonIndependentConditionalScalarConvention.original (V:=V) (U:=V) L (fun _ _ _=>rfl) false true (k+1) W
  apply ((WilsonIndependentConditionalInsertion.original S F H Q hf volume hp ratio wp branch sym pure wpure b).2 _).mp
  rw [WilsonIndependentConditionalInsertion.one,WilsonIndependentConditionalInsertion.zero,←formv,←formw,
    ←map_mul,←map_mul,pre,pre]
  change _=_*PowerSeries.map (emphasis X).toRingHom
    (rated (fun e=>e+(k+1)) (endHeat (k+1) L (logHeat L V false) W))
  rw [conv]
  simpa only [Nat.add_assoc] using eqn

end YM.Integration.WilsonIndependentConditionalHeardMean
