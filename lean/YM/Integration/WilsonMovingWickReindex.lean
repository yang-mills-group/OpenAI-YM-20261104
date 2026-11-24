import YM.Integration.WilsonConditionalTaylorWick
import YM.Integration.WilsonMovingPolynomialPull
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Projection

/-! The finite conditional survives changing the order of the actual forest
and fine coordinates. The observable placement may identify labels; the
Gaussian variables themselves are permuted bijectively. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingWickReindex
open Function Matrix PowerSeries MeasureTheory FormalBulk08 Next.SectorChange MSbar.Cacao
open WilsonMovingPolynomialPull WilsonConditionalTaylorWick
open scoped Classical BigOperators Matrix
variable {I J K L : Type}

def position (e : I ≃ K) : (K → ℝ) ≃ᵐ (I → ℝ) where
  toFun z := z ∘ e
  invFun z := z ∘ e.symm
  left_inv z := funext fun i => by simp
  right_inv z := funext fun i => by simp
  measurable_toFun := measurable_pi_lambda _ fun i => measurable_pi_apply (e i)
  measurable_invFun := measurable_pi_lambda _ fun i => measurable_pi_apply (e.symm i)

theorem field [Fintype I] [Fintype K] (B : Matrix L K ℝ) (x : L→ℝ) (s : J→L)
    (e : I ≃ K) (z : K→ℝ) :
    (x ∘ s) + B.submatrix s e *ᵥ (z ∘ e) = (x+B*ᵥz) ∘ s := by
  funext j
  change x (s j) + ∑ i, B (s j) (e i)*z (e i) = x (s j) + ∑ k, B (s j) k*z k
  rw [e.sum_comp (fun k => B (s j) k*z k)]

variable [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
variable (B : Matrix L K ℝ) (x : L→ℝ) (Q : Matrix K K ℝ) (pos : Q.PosDef)
    (s : J→L) (e : I ≃ K)
include pos

theorem integrated (T : PowerSeries (MvPolynomial J ℝ)) :
    WilsonMovingGaussianResponse.numerator (Q.submatrix e e) (B.submatrix s e) (x ∘ s) T =
      WilsonMovingGaussianResponse.numerator Q B x (place s T) := by
  ext n
  simp only [WilsonMovingGaussianResponse.numerator,coeff_mk,place,PowerSeries.coeff_map]
  have projection : MeasurePreserving (position e) (Gaussian.cloud Q) (Gaussian.cloud (Q.submatrix e e)) :=
    AnalyticBridge.Sharp.Projection.cloud_projection pos e
  rw [← projection.integral_comp' (fun z => MvPolynomial.eval ((x ∘ s)+B.submatrix s e *ᵥ z) (coeff n T))]
  apply integral_congr_ae
  filter_upwards with z
  change MvPolynomial.eval ((x ∘ s)+B.submatrix s e *ᵥ (z ∘ e)) (coeff n T) =
    MvPolynomial.eval (x+B*ᵥz) ((MvPolynomial.rename s) (coeff n T))
  rw [field, MvPolynomial.eval_rename]

theorem contracted (T : PowerSeries (MvPolynomial J ℝ)) :
    contract (B.submatrix s e) (x ∘ s) (Q.submatrix e e) T =
      contract B x Q (place s T) := by
  have sym : Q.IsSymm := by ext i j; exact pos.isHermitian.apply i j
  have hs : (Q.submatrix e e).IsSymm := by ext i j; exact sym.apply (e i) (e j)
  unfold contract
  rw [← WilsonMovingWickCoefficient.complete _ _ _ hs (pos.posSemidef.submatrix e),
    ← WilsonMovingWickCoefficient.complete _ _ _ sym pos.posSemidef]
  exact integrated B x Q pos s e T

theorem normalized (f T : PowerSeries (MvPolynomial J ℝ)) :
    quotient (B.submatrix s e) (x ∘ s) (Q.submatrix e e) f T =
      quotient B x Q (place s f) (place s T) := by
  unfold quotient
  rw [contracted B x Q pos s e,contracted B x Q pos s e]
  simp only [place,map_mul,sunshine]

end YM.Integration.WilsonMovingWickReindex
end
