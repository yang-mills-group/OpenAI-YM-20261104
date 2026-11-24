import YM.Integration.FVA1Physical.Wilson.QuadraticTaylor
import YM.Comparison.RG02.Cumulants.Cloud

/-! Transfer the true conditional Gaussian integration-by-parts rule to
symmetric real Taylor tensors of any finite arity, with all coordinates and
repeated indices on the original finite torus. -/
set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson.SignCovariance
open Finset Function Matrix MeasureTheory Push.Uniform YM.Tensor
open YM.Next.Rank YM.Next.SectorChange YM.Comparison.RG02.Cumulants YM.PhysicalNext.WeightedGaussianMarginal45C
open scoped BigOperators Classical Topology ContDiff
variable {ι:Type} [Fintype ι] [DecidableEq ι] {d:ℕ}
local notation "V" => (ι→ℝ)

private def tensorPolynomial (T:Tensor.T V ℝ d) : Normal.poly ι :=
  ∑ a:Fin d→ι, (∏ k,MvPolynomial.X (a k))*MvPolynomial.C (T (fun k=>bolt (a k)):ℂ)

omit [DecidableEq ι] in
private theorem tensorPaint (T:Tensor.T V ℝ d) (z:V) : Cloud.paint z (tensorPolynomial T)=Complex.ofReal (Tensor.diagonal T z) := by
  rw [show Tensor.diagonal T z=T (fun _=>z) from rfl,multi_expansion T]
  unfold tensorPolynomial Cloud.paint
  simp only [map_sum,_root_.map_mul,map_prod,MvPolynomial.aeval_X,MvPolynomial.aeval_C,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod,Algebra.algebraMap_self,RingHom.id_apply]

omit [DecidableEq ι] in
private theorem coordPaint (T:Tensor.T V ℝ d) (i:ι) (z:V) : Cloud.paint z (MvPolynomial.X i*tensorPolynomial T)=Complex.ofReal (z i*Tensor.diagonal T z) := by
  rw [_root_.map_mul,MvPolynomial.aeval_X,tensorPaint,Complex.ofReal_mul]

theorem tensorCoordIntegrable (K:Matrix ι ι ℝ) (pd:K.PosDef) (T:Tensor.T V ℝ d) (i:ι) :
    Integrable (fun z:V=>z i*Tensor.diagonal T z) (Gaussian.cloud K) := by
  have P:=Issue.fullGlyph K pd.posSemidef (isHermitian_iff_isSymm.mp pd.isHermitian)
  have h:Integrable (fun z=>Cloud.paint z (MvPolynomial.X i*tensorPolynomial T)) (Gaussian.cloud K):=P.prices _
  exact (Complex.reCLM.integrable_comp h).congr (.of_forall fun z=>by change (Cloud.paint z _).re=_;rw [coordPaint];rfl)

theorem tensorIntegrable (K:Matrix ι ι ℝ) (pd:K.PosDef) (T:Tensor.T V ℝ d) :
    Integrable (Tensor.diagonal T) (Gaussian.cloud K) := by
  have P:=Issue.fullGlyph K pd.posSemidef (isHermitian_iff_isSymm.mp pd.isHermitian)
  have h:Integrable (fun z=>Cloud.paint z (tensorPolynomial T)) (Gaussian.cloud K):=P.prices _
  exact (Complex.reCLM.integrable_comp h).congr (.of_forall fun z=>by change (Cloud.paint z _).re=_;rw [tensorPaint];rfl)

/-- Direct equality of the ordinary numerical integral of a coordinate times a
symmetric form with the Gaussian covariance contraction of one Taylor slot. -/
theorem tensor_stein (K:Matrix ι ι ℝ) (pd:K.PosDef) (T:Tensor.T V ℝ (d+1))
    (sym:Tensor.Sym T) (i:ι) :
    (∫ z:V,z i * Tensor.diagonal T z ∂Gaussian.cloud K) =
      ∫ z:V,(d+1:ℝ)*Tensor.diagonal (T.curryLeft (K i)) z ∂Gaussian.cloud K := by
  let hS:=isHermitian_iff_isSymm.mp pd.isHermitian
  let P:=Issue.fullGlyph K pd.posSemidef hS
  let p:=tensorPolynomial T
  let q:=Normal.slit ((Issue.realRank K hS).cov i) p
  let f:=fun z:V=>Cloud.paint z p
  have source : f = Complex.ofRealCLM ∘ Tensor.diagonal T := funext fun z=>tensorPaint T z
  have hi:Integrable (fun z=>Cloud.paint z (MvPolynomial.X i*p)) (Gaussian.cloud K):=P.prices _
  have hd:Integrable (fun z=>Cloud.paint z q) (Gaussian.cloud K):=P.prices _
  have sameL : Issue.lenses (1:Matrix ι ι ℝ) p=f := funext fun z=>by unfold Issue.lenses;rw [Matrix.one_mulVec];rfl
  have der(z:V):fderiv ℝ f z (K i) = Cloud.paint z q := by
    have h := (Issue.derives (1:Matrix ι ι ℝ) p (K i)).2 z
    rw [sameL] at h
    change _ = Cloud.paint z q
    simpa only [Issue.lenses,Matrix.one_mulVec, q,Issue.realRank,peval,Cloud.paint] using h
  have read(z:V) : (Cloud.paint z q).re=(d+1:ℝ)*Tensor.diagonal (T.curryLeft (K i)) z := by
    have hdg : DifferentiableAt ℝ (Tensor.diagonal T) z := (Tensor.diag_smooth T ω).contDiffAt.differentiableAt (by simp)
    rw [←der,source,fderiv_comp z Complex.ofRealCLM.differentiableAt hdg,Complex.ofRealCLM.fderiv,ContinuousLinearMap.comp_apply,Tensor.differential_diagonal T sym]
    simp [Tensor.diagonal, nsmul_eq_mul]
  calc
    _ = ∫ z,(Cloud.paint z (MvPolynomial.X i*p)).re ∂Gaussian.cloud K := by
      apply integral_congr_ae;apply Filter.Eventually.of_forall;intro z
      change _=(Cloud.paint z (MvPolynomial.X i*tensorPolynomial T)).re
      rw [coordPaint];rfl
    _ = (∫ z,Cloud.paint z (MvPolynomial.X i*p) ∂Gaussian.cloud K).re := Complex.reCLM.integral_comp_comm hi
    _ = (∫ z,Cloud.paint z q ∂Gaussian.cloud K).re := congrArg Complex.re (P.ibp p i)
    _ = ∫ z,(Cloud.paint z q).re ∂Gaussian.cloud K := (Complex.reCLM.integral_comp_comm hd).symm
    _ = _ := integral_congr_ae (.of_forall read)

end YM.Integration.FVA1Physical.Wilson.SignCovariance
