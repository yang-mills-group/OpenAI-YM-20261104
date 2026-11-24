import YM.Integration.WilsonIndependentConditionalScale
import YM.Integration.WilsonIndependentPublicReportBias

/-! At the actually purchased positive report scale, integrate every term of
the finite Wood/Wick polynomial on its actual normalized Gaussian law. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentConditionalFiniteClock
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Convention RegulatorIR RegulatorIR.Calibration RegulatorIR.Profiles
open PertExtension PertExtension.GaussianScore MeasureTheory PowerSeries
open Lattice FreeResolvent Metric RG Wilson Tree Precision Matrix Exterior
open WilsonIndependentConditionalScale
open scoped Classical BigOperators MatrixOrder

def partialSum {I:Type}(P:Ink I)(j:ℕ)(g:ℝ)(b:Lawn I):ℝ:=
  ∑ e∈Finset.range (j+1),g^e*MvPolynomial.eval b (coeff e P)

variable {G:Gauge}{c f:Side}(S:StepData c f)(T:Forest S.ratio)(H:FaceRow)
  (Q:Matrix (Body 1 f) (Body 1 c) ℝ)

def tilted (hf:(treeMatrix G S T H).PosDef)(K:Feeds)(q:ℕ)(t:ℝ)(b:TreeVars G c)
    (D:Ink (Active G T ⊕ Woods G c)):ℝ:=
  (law hf).average volume (fun x=>bias (law hf) (K.dine t) x*
    partialSum D q (t*K.dine t) (Sum.elim ((K.dine t)⁻¹ • x) ((K.dine t)⁻¹ • b)))

theorem polynomial (hf:(treeMatrix G S T H).PosDef)(K:Feeds)(q:ℕ)(t:ℝ)(b:TreeVars G c)
    (D:Ink (Active G T ⊕ Woods G c)):
    tilted S T H hf K q t b D=(K.dine t)^Module.finrank ℝ (Lawn (Active G T))*
    partialSum (Wick (Woods G c) (treeInverse G S T H 0) D) q (t*K.dine t) ((K.dine t)⁻¹ • b):=by
  let v:TreeVars G c:=(K.dine t)⁻¹ • b
  let g:=t*K.dine t
  have inv:treeMatrix G S T H*treeInverse G S T H 0=1:=by
    simp only [treeInverse,resolve,zero_smul,add_zero]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hf.det_pos.ne')
  have sy:(treeInverse G S T H 0).transpose=treeInverse G S T H 0:=by
    have hh:(treeMatrix G S T H).transpose=treeMatrix G S T H:=Matrix.isHermitian_iff_isSymm.mp hf.isHermitian
    simp only [treeInverse,resolve,zero_smul,add_zero,transpose_nonsing_inv,hh]
  have read (i:ℕ):
      (law hf).average volume (sectionPoly v (coeff i D))=
        MvPolynomial.eval v (coeff i (Wick (Woods G c) (treeInverse G S T H 0) D)):=by
    exact (gaussian_polynomial_coeff volume hf v inv sy D i).symm
  unfold tilted
  rw [WilsonIndependentConditionalScale.original volume (law hf) _ (K.positive t)
    (fun x=>partialSum D q g (Sum.elim x v))]
  congr 1
  change (law hf).average volume (fun x=>∑i∈_,g^i*sectionPoly v (coeff i D) x)=_
  unfold partialSum
  change _=∑i∈_,g^i*MvPolynomial.eval v (coeff i (Wick (Woods G c) (treeInverse G S T H 0) D))
  simp_rw [←read,Law.average,Pi.mul_apply,Finset.sum_mul,mul_assoc]
  rw [integral_finsetSum,Finset.sum_div]
  · refine Finset.sum_congr rfl fun i _=>?_
    rw [integral_const_mul,mul_div_assoc]
  · intro i _
    exact (section_integrable volume hf v (coeff i D)).const_mul _

theorem original (hf:(treeMatrix G S T H).PosDef)(K:Feeds)(q:ℕ)(t:ℝ)(b:TreeVars G c)
    (Ñ:ChartRatio G)(P w:PChart G f):
    let e:=raiseE (shot S T Q Ñ P)
    let h:=loom (camSlice G S T (extractV G S T Q)) (flash w)
    tilted S T H hf K q t b (e*h)/tilted S T H hf K q t b e=
      partialSum (insideMark S T H Q Ñ P w) q (t*K.dine t) ((K.dine t)⁻¹ • b)/
      partialSum (inside S T H Q Ñ P) q (t*K.dine t) ((K.dine t)⁻¹ • b):=by
  dsimp only
  rw [polynomial,polynomial]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (K.positive t).ne')

end YM.Integration.WilsonIndependentConditionalFiniteClock
