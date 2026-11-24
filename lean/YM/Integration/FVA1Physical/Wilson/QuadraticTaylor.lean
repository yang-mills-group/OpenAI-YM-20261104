import YM.Integration.FVA1Physical.Wilson.QuadraticCloud
import YM.Comparison.RG02.Valence.Level
import YM.Push.STATIONARY_UNIFORM.Touch

/-! Any actual finite quadratic, with its constant and linear terms, has
a dimension-independent Gaussian reconstruction fee from the supremum on
a deterministic cube and the covariance row price. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson.SignCovariance
open Function Finset MeasureTheory Matrix Push.Uniform Comparison.RG02 Valence
open YM.Next.SectorChange YM.AnalyticBridge.LocalGaussianLaws
open scoped BigOperators Classical ContDiff Topology

variable {ι:Type} [Fintype ι] [DecidableEq ι]
private def tensorMatrix (T : Tensor.T (ι→ℝ) ℝ 2) : Matrix ι ι ℝ := fun i j=>
    T (fun k=>bolt ((finTwoArrowEquiv ι).symm (i,j) k))

omit [DecidableEq ι] in
private theorem tensor_matrix (T:Tensor.T (ι→ℝ) ℝ 2) (s:Tensor.Sym T) :
    (tensorMatrix T).IsSymm := by
  ext i j
  let v : Fin 2→(ι→ℝ):=fun k=>bolt ((finTwoArrowEquiv ι).symm (i,j) k)
  have e : (fun k=>bolt ((finTwoArrowEquiv ι).symm (j,i) k)) = v ∘ Equiv.swap 0 1 := by
    funext k;fin_cases k <;> simp [v,Function.comp,finTwoArrowEquiv]
  exact (congrArg T e).trans (s v _)

omit [DecidableEq ι] in
private theorem tensor_read (T:Tensor.T (ι→ℝ) ℝ 2) (z:ι→ℝ) :
    Tensor.diagonal T z = bilinear (tensorMatrix T) z z := by
  change T (fun _=>z) = _
  rw [multi_expansion T,← Equiv.sum_comp (finTwoArrowEquiv ι).symm,Fintype.sum_prod_type]
  unfold bilinear
  apply sum_congr rfl;intro i _
  apply sum_congr rfl;intro j _
  simp only [Fin.prod_univ_two,tensorMatrix]
  change z i*z j*_ = _*z i*z j
  ring

private theorem linear_read (L:(ι→ℝ)→L[ℝ]ℝ) (K:Matrix ι ι ℝ) :
    Integrable L (Gaussian.cloud K) ∧ ∫ z,L z ∂Gaussian.cloud K=0 := by
  have e (z:ι→ℝ) : L z = ∑ i,z i*L (bolt i) := by
    calc L z = L (∑ i,z i • bolt i) := congrArg L (combine z).symm
         _ = _ := by rw [map_sum]; simp only [map_smul,smul_eq_mul]
  have h (i:ι) : Integrable (fun z:ι→ℝ=>z i*L (bolt i)) (Gaussian.cloud K) :=
    ((Density.first_debit K i).integrable (by norm_num)).mul_const _
  constructor
  · exact (integrable_finsetSum _ fun i _=>h i).congr (.of_forall fun z=>(e z).symm)
  · rw [show (fun z:ι→ℝ=>L z) = (fun z=>∑ i,z i * L (bolt i)) from funext e]
    rw [integral_finsetSum _ fun i _=>h i]
    simp [integral_mul_const,Gaussian.cloud_center]

theorem level_two_expectation (f:(ι→ℝ)→ℝ) (degree:Level 2 f) (K:Matrix ι ι ℝ)
    (pd:K.PosDef) {a C δ:ℝ} (ha:0<a) (hc:0≤C) (rows:∀i,∑ j,|K i j|≤C)
    (cube:∀z,‖z‖≤a→|f z|≤δ) :
    |∫ z, f z ∂Gaussian.cloud K| ≤ δ + 4*(1+C)*δ/a^2 := by
  let μ:=Gaussian.cloud K
  let L:=fderiv ℝ f 0
  let T:=Tensor.coeff f 2 0
  let W:=tensorMatrix T
  have sym:=tensor_matrix T (Tensor.coeff_symm (degree.smooth.contDiffAt.of_le (by simp)))
  have rep (z:ι→ℝ) : f z = f 0+L z+bilinear W z z := by
    have h:=Level.posted (r:=2) degree z
    simpa only [sum_range_succ,sum_range_zero,zero_add,Assembly.jet_zero,
        show Assembly.jet f 1 z = L z by simp [Assembly.jet,iteratedFDeriv_one_apply,L],
        show Assembly.jet f 2 z = bilinear W z z from tensor_read T z] using h
  have zero:= cube 0 (by simpa using ha.le)
  have small (z:ι→ℝ) (hz:‖z‖≤a) : |bilinear W z z| ≤ 2*δ := by
    have neg : bilinear W (-z) (-z)=bilinear W z z := by simp [bilinear]
    have hp:=cube z hz
    have hn:=cube (-z) (by simpa using hz)
    rw [rep z] at hp
    rw [rep (-z),map_neg,neg] at hn
    exact abs_le.mpr ⟨by linarith only [abs_le.mp hp,abs_le.mp hn,abs_le.mp zero],
      by linarith only [abs_le.mp hp,abs_le.mp hn,abs_le.mp zero]⟩
  have quad : Integrable (fun z:ι→ℝ=>bilinear W z z) μ := by
    apply integrable_finsetSum;intro i _
    apply integrable_finsetSum;intro j _
    simp_rw [mul_assoc]
    exact ((Density.first_debit K i).integrable_mul (Density.first_debit K j)).const_mul _
  have l:=linear_read L K
  have e : (∫ z,f z ∂μ)=f 0+∫ z,bilinear W z z ∂μ := by
    have h0 : Integrable (fun _:ι→ℝ=>f 0) μ := integrable_const _
    have hL : Integrable (fun z:ι→ℝ=>L z) μ := l.1
    have both : Integrable (fun z:ι→ℝ=>f 0+L z) μ := h0.add hL
    calc _ = ∫ z,f 0+L z+bilinear W z z ∂μ := integral_congr_ae (.of_forall rep)
         _ = _ := by rw [integral_add both quad,integral_add h0 hL,l.2]; simp [μ]
  rw [e]
  refine (abs_add_le ..).trans (add_le_add zero ?_)
  rw [quadratic_gaussian W K pd]
  exact (cube_contraction W K sym ha hc rows small).trans_eq (by ring)
end YM.Integration.FVA1Physical.Wilson.SignCovariance
