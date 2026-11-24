import YM.Integration.WilsonIndependentConditionalNotebookFilm

/-! Compare the actual two marked conditional renderers before their remaining field is set. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonIndependentConditionalDiagramResponse
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Convention RegulatorIR RegulatorIR.Diagram
open PertExtension PertExtension.GaussianScore MeasureTheory PowerSeries
open Lattice FreeResolvent Metric RG Wilson Tree Precision Matrix Exterior
open WilsonIndependentConditionalHeldGaussian WilsonIndependentConditionalNotebookFilm
open scoped Classical BigOperators MatrixOrder
variable {G:Gauge}{c f:Side} (S:StepData c f)(F:Forest S.ratio)(H:FaceRow)
   (Q:Matrix (Body 1 f) (Body 1 c) ℝ)

def old (Ñ:ChartRatio G)(P:PChart G f):Orders (Active G F⊕Woods G c):=
  fun i=>fade (overM G S F) (casePW S Ñ (extractV G S F Q) P i)
def mark (w:PChart G f):Orders (Active G F⊕Woods G c):=
  fun i=>fade (camSlice G S F (extractV G S F Q)) (w i)
def lines := fillSlots (Woods G c) (treeInverse G S F H 0)
def response (Ñ:ChartRatio G)(P w:PChart G f)(l:ℕ):Ink (Active G F⊕Woods G c):=
  let K:=lines S F H
  rated (fun e=>e+l) (endHeat l K (logHeat K (old S F Q Ñ P) true) (mark S F Q w))

theorem heard {Ñ:ChartRatio G}{P w:PChart G f}{m:ℕ}(p:shellK 2 P)(ratio:LocalRatio Ñ)
    (oper:shellK (m+1) w)(branch:S.patch.Branches S.kernel G)(sym:(H.acts f).transpose=H.acts f)
    (pure:∀ i,Pure (P i))(wpure:∀ i,Pure (w i))(hf:(treeMatrix G S F H).PosDef)
    (μ:Measure (Lawn (Active G F))) [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ]
    (b:Woods G c→ℝ):
    PowerSeries.map (emphasis (held b)).toRingHom (response S F H Q Ñ P w (m+1))=
      PowerSeries.map (emphasis b).toRingHom (flash (reed S F H Q Ñ P (m+1) w)) :=by
  classical
  let V:=old S F Q Ñ P
  let R:=mark S F Q w
  let T:=treeMatrix G S F H
  let cov:=lines (G:=G) S F H
  let law:=Convention.law hf
  let d:=noise (J:=Woods G c) (tooth (X:=Active G F))
  have vp:shellK 2 V:=fade_shell _ (pack_band S p)
  have rp:shellK (m+1) R:=fade_shell _ oper
  have v0:V 0=0:=by
    ext1 r;funext x
    simp [V,old,pack_zero S ratio,fade]
  have vg:gradedSymmetric V:=fun i=>fade_pure (pack_pure S ratio branch pure i) _
  have rg:gradedSymmetric R:=fun i=>fade_pure (wpure i) _
  have vfilm: rated (fun e=>e+2) V=shot S F Q Ñ P:=
    (film vp).trans (loom_fade _ _ (finite_shell (pack_band S p))).symm
  have rfilm: rated (fun e=>e+(m+1)) R=loom (camSlice G S F (extractV G S F Q)) (flash w):=
    (film rp).trans (loom_fade _ _ (finite_shell oper)).symm
  have z0:constantCoeff (shot S F Q Ñ P)=0:=by
    rw [←vfilm,←coeff_zero_eq_constantCoeff_apply,rated,coeff_mk,v0]
    simp [packed,render]
  have bonds: Gaussian.bond law d=cov:=by
    rw [show Gaussian.bond law d=fillSlots _ (Gaussian.bond law (tooth (X:=Active G F))) from pad ..]
    unfold cov lines treeInverse resolve
    rw [zero_smul,add_zero]
    congr 1;funext i j
    rw [Gaussian.bond_cross,Gaussian.bond,inverse_tooth hf (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hf.det_pos.ne'))]
  have equation:=green law d μ m V R (held b) (vacuum vp v0) vg (within rp) rg
  dsimp only at equation
  have a:=WilsonIndependentConditionalInsertion.original S F H Q hf μ p ratio oper branch sym pure wpure b
  apply (a.2 _).mp
  rw [WilsonIndependentConditionalInsertion.one,WilsonIndependentConditionalInsertion.zero]
  change burn law d μ _ _ = burn law d μ _ _ * _
  simp only [Nat.add_assoc] at equation
  rw [bonds,vfilm,exponential z0,rfilm] at equation
  exact equation

private theorem restrict {I J:Type}(b:J→ℝ)(p:POL (I⊕J)):
    emphasis b (projectZeroPoly I J p)=emphasis (held b) p:=by
  induction p using MvPolynomial.induction_on with
  | C c=>simp [emphasis,projectZeroPoly]
  | add p q hp hq=>simp only [map_add,hp,hq]
  | mul_X p i h=>
    rw [map_mul,map_mul,map_mul,h]
    cases i <;>simp [emphasis,held,projectZeroPoly]

theorem original {Ñ:ChartRatio G}{P w:PChart G f}{m:ℕ}(p:shellK 2 P)(ratio:LocalRatio Ñ)
    (oper:shellK (m+1) w)(branch:S.patch.Branches S.kernel G)(sym:(H.acts f).transpose=H.acts f)
    (pure:∀ i,Pure (P i))(wpure:∀ i,Pure (w i))(hf:(treeMatrix G S F H).PosDef):
    projectZero (response S F H Q Ñ P w (m+1))=
      flash (reed S F H Q Ñ P (m+1) w) :=by
  ext1 e
  apply MvPolynomial.funext
  intro b
  have h:=congrArg (coeff e) (heard S F H Q p ratio oper branch sym pure wpure hf volume b)
  simp only [coeff_map] at h
  rw [←MvPolynomial.aeval_eq_eval]
  change (emphasis b) ((coeff e) (PowerSeries.map _ _)) = (emphasis b) _
  rw [coeff_map]
  exact (restrict b _).trans h

end YM.Integration.WilsonIndependentConditionalDiagramResponse
