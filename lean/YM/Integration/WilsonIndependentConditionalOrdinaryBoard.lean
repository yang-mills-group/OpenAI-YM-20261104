import YM.Integration.WilsonIndependentConditionalFullAxes
import YM.Integration.WilsonIndependentConditionalScalarConvention

/-! The actual normalized one-source conditional on ordinary finite full link
coordinates, before contraction in the retained field. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalOrdinaryBoard
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Convention RegulatorIR RegulatorIR.Diagram
open WilsonIndependentConditionalHeldGaussian WilsonIndependentConditionalNotebookFilm
open PertExtension PertExtension.GaussianScore MeasureTheory PowerSeries
open Lattice FreeResolvent Metric RG Wilson Tree Precision Matrix Exterior
open scoped Classical BigOperators MatrixOrder

variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)
   (H:FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)

def response (Ñ:ChartRatio G)(P w:PChart G f)(l:ℕ):Ink (Joint G f c):=
  let M:=extractV G S F Q
  let L:=fillSlots (Woods G c) (covariance G S F H)
  rated (fun e=>e+l) (endHeat l L (logHeat L (casePW S Ñ M P) false) (srCold w M))

theorem original {Ñ:ChartRatio G}{P w:PChart G f}{k:ℕ}(hp:shellK 2 P)(ratio:LocalRatio Ñ)
    (wp:shellK (k+1) w)(branch:S.patch.Branches S.kernel G)(sym:(H.acts f).transpose=H.acts f)
    (pure:∀ i,Pure (P i))(wpure:∀ i,Pure (w i))(hf:(treeMatrix G S F H).PosDef)(b:Woods G c→ℝ):
    PowerSeries.map (emphasis (held b)).toRingHom (response S F H Q Ñ P w (k+1))=
       PowerSeries.map (emphasis b).toRingHom (flash (reed S F H Q Ñ P (k+1) w)):=by
  let M:=extractV G S F Q
  let V:=casePW S Ñ M P
  let W:=srCold w M
  let d:=WilsonIndependentConditionalFullAxes.lifted (G:=G) S F
  let chart:=overM G S F
  have vs:shellK 2 V:=pack_band S hp
  have zero:V 0=0:=pack_zero S ratio
  have ws:shellK (k+1) W:=fade_shell _ wp
  have formv:loom chart (Formal.expo (rated (fun e=>e+2) V))=raiseE (shot S F Q Ñ P):=by
    rw [film vs]
    change PowerSeries.map (cord chart).toRingHom (Formal.expo (flash V))=_
    rw [Formal.map_exp,show PowerSeries.map (cord chart).toRingHom (flash V)=shot S F Q Ñ P from rfl]
    apply exponential
    change constantCoeff (PowerSeries.map _ (flash V))=0
    rw [←coeff_zero_eq_constantCoeff_apply,coeff_map,flash,coeff_mk,zero]
    simp [totalR]
  have formw:loom chart (rated (fun e=>e+(k+1)) W)=loom (camSlice G S F M) (flash w):=by
    rw [film ws,show flash W=loom (camber G M) (flash w) from (loom_fade _ w (finite_shell wp)).symm]
    exact DFunLike.congr_fun (loom_loom (camber G M) chart) (flash w)
  have eqn:=green (law hf) d volume k V W (held b) (vacuum vs zero) (pack_pure S ratio branch pure)
    (within ws) (fun i=>fade_pure (wpure i) _)
  have line:=WilsonIndependentConditionalFullAxes.original S F H hf
  rw [show Gaussian.bond (law hf) d=fillSlots (Woods G c) (covariance G S F H) from line] at eqn
  let L:=fillSlots (Woods G c) (covariance G S F H)
  have convention := WilsonIndependentConditionalScalarConvention.original (V:=V) (U:=V) L (fun _ _ _=>rfl) false true (k+1) W
  have comp:=WilsonIndependentConditionalInsertion.original S F H Q hf volume hp ratio wp branch sym pure wpure b
  apply (comp.2 _).mp
  rw [WilsonIndependentConditionalInsertion.one,WilsonIndependentConditionalInsertion.zero]
  unfold WilsonIndependentConditionalInsertion.read
  rw [←formv,←formw,←map_mul,
     WilsonIndependentConditionalFullAxes.hearing,WilsonIndependentConditionalFullAxes.hearing]
  change _=_*PowerSeries.map _ (rated _ (endHeat _ L (logHeat L V false) W))
  rw [convention]
  simpa only [Nat.add_assoc] using eqn

end YM.Integration.WilsonIndependentConditionalOrdinaryBoard
