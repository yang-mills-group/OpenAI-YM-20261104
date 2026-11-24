import YM.Integration.WilsonIndependentConditionalDiagramResponse
import YM.Integration.WilsonIndependentConditionalScalarConvention
import YM.RegulatorIR.Binding.Rafter

/-! Exact complete unmarked log on a finite ordinary tree, including its
older constant. The diagram and the Wilson step use one conditional law. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentConditionalVacuum
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Convention RegulatorIR RegulatorIR.Diagram
open PertExtension PertExtension.GaussianScore MeasureTheory PowerSeries
open Lattice FreeResolvent Metric RG Wilson Tree Precision Matrix Exterior
open WilsonIndependentConditionalHeldGaussian WilsonIndependentConditionalNotebookFilm
open WilsonIndependentConditionalDiagramResponse
open scoped Classical BigOperators MatrixOrder
variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)(H:FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)

def raw (Ñ:ChartRatio G)(P:PChart G f):Ink (Active G F⊕Woods G c):=
  rated (fun e=>e+2) (ceaseHeat (lines S F H) (old S F Q Ñ P) true)

private theorem restrict {I J:Type}(b:J→ℝ)(p:POL (I⊕J)):
    emphasis b (projectZeroPoly I J p)=emphasis (held b) p:=by
  induction p using MvPolynomial.induction_on with
  | C a=>simp [emphasis,projectZeroPoly]
  | add p q hp hq=>simp only [map_add,hp,hq]
  | mul_X p i h=>
    rw [map_mul,map_mul,map_mul,h]
    cases i <;>simp [emphasis,held,projectZeroPoly]

theorem heat {Ñ:ChartRatio G}{P:PChart G f}(p:shellK 2 P)(ratio:LocalRatio Ñ)
    (branch:S.patch.Branches S.kernel G)(pure:∀ i,Pure (P i))
    (hf:(treeMatrix G S F H).PosDef):
    constantCoeff (raw S F H Q Ñ P)=0 ∧
    projectZero (Formal.expo (raw S F H Q Ñ P))=inside S F H Q Ñ P :=by
  let V:=old S F Q Ñ P
  let L:=law hf
  let d:=noise (J:=Woods G c) (tooth (X:=Active G F))
  have vp:shellK 2 V:=fade_shell _ (pack_band S p)
  have v0:V 0=0:=by ext1 r;funext x;simp [V,old,pack_zero S ratio,fade]
  have vg:gradedSymmetric V:=fun i=>fade_pure (pack_pure S ratio branch pure i) _
  have vv:=vacuum vp v0
  have vfilm:rated (fun e=>e+2) V=shot S F Q Ñ P:=
    (film vp).trans (loom_fade _ _ (finite_shell (pack_band S p))).symm
  have z0:constantCoeff (shot S F Q Ñ P)=0:=by
    rw [←vfilm,←coeff_zero_eq_constantCoeff_apply,rated,coeff_mk,v0]
    simp [packed,render]
  have bonds:Gaussian.bond L d=lines (G:=G) S F H:=by
    rw [show Gaussian.bond L d=fillSlots _ (Gaussian.bond L (tooth (X:=Active G F))) from pad ..]
    unfold lines treeInverse resolve
    rw [zero_smul,add_zero]
    congr 1;funext i j
    rw [Gaussian.bond_cross,Gaussian.bond,inverse_tooth hf (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hf.det_pos.ne'))]
  have zero:ceaseHeat (lines (G:=G) S F H) V true 0=0:=by
    funext r
    by_contra nz
    exact (Nat.lt_irrefl 0) (Binding.warmed _ _ vv _ _ nz).1
  constructor
  · rw [raw,←coeff_zero_eq_constantCoeff_apply,rated,coeff_mk]
    change packed (ceaseHeat _ V true 0) _=0
    rw [zero];simp [packed,render]
  ext1 e
  apply MvPolynomial.funext
  intro b
  have actual:=red L d volume V (held b) vv vg
  rw [bonds,vfilm,exponential z0] at actual
  have read:=WilsonIndependentConditionalInsertion.reading hf volume b (raiseE (shot S F Q Ñ P))
  change burn L d volume _ (held b)=_ at read
  have cov:treeInverse G S F H 0=(treeMatrix G S F H)⁻¹:=by simp [treeInverse,resolve]
  rw [←cov] at read
  have eq:=congrArg (coeff e) (actual.symm.trans read)
  simp only [coeff_map] at eq
  rw [←MvPolynomial.aeval_eq_eval]
  change emphasis b ((coeff e) (PowerSeries.map _ _)) = emphasis b _
  rw [coeff_map]
  exact (restrict b _).trans eq

theorem original {Ñ:ChartRatio G}{P:PChart G f}(p:shellK 2 P)(ratio:LocalRatio Ñ)
    (branch:S.patch.Branches S.kernel G)(sym:(H.acts f).transpose=H.acts f)
    (pure:∀ i,Pure (P i))(hf:(treeMatrix G S F H).PosDef):
    projectZero (raw S F H Q Ñ P)=flash (summer S F H Q Ñ P) :=by
  have h:=heat S F H Q p ratio branch pure hf
  have zz:constantCoeff (projectZero (raw S F H Q Ñ P))=0:=by
    rw [←coeff_zero_eq_constantCoeff_apply,projectZero,coeff_map,coeff_zero_eq_constantCoeff_apply,h.1,map_zero]
  rw [wedgeW S F H Q p ratio branch sym pure]
  apply raise_inj zz (constantCoeff_logOf (inside_mass S F H Q ratio))
  rw [raising_log (inside_mass S F H Q ratio)]
  rw [←exponential zz,projectZero,←Formal.map_exp]
  exact h.2

end YM.Integration.WilsonIndependentConditionalVacuum
