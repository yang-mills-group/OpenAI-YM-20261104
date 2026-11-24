import YM.Integration.WilsonMovingNormalizedBank
import YM.Integration.MSFixedRatioSaddleWick

/-! The unrestricted posterior's homogeneous Gaussian integral is the
original independent finite Wick moment, at its actual affine mean and
complete covariance, on every real polynomial, including products. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingWickCoefficient
open Function PowerSeries Matrix MeasureTheory MvPolynomial
open FormalBulk08 Wick Series Comparison.RG02 Cumulants Next.SectorChange MSbar.Cacao
open scoped Classical BigOperators Matrix
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] [DecidableEq I] in
theorem observed (x : I → ℝ) (p : MvPolynomial I ℝ) :
    Cloud.paint x (MvPolynomial.map Complex.ofRealHom p) = (MvPolynomial.eval x p : ℂ) := by
  exact (MvPolynomial.map_eval Complex.ofRealHom x p).symm

theorem gaussian (Q : Matrix I I ℝ) (sym : Q.IsSymm) (positive : Q.PosSemidef)
    (p : MvPolynomial I ℝ) :
    (∫ z, MvPolynomial.eval z p ∂Gaussian.cloud Q) = Wick.moment Q p := by
  apply Complex.ofReal_injective
  rw [← MSFixedRatioSaddleWick.moment Q sym p]
  calc
    _ = ∫ z, (MvPolynomial.eval z p : ℂ) ∂Gaussian.cloud Q :=
      (integral_ofReal (𝕜:=ℂ) (μ:=Gaussian.cloud Q)
        (f:=fun z => MvPolynomial.eval z p)).symm
    _ = _ := ?_
  have h := (Cloud.paid Q sym positive (0 : I → ℝ) (MvPolynomial.map Complex.ofRealHom p)).2
  simpa only [zero_add, observed, show Cloud.shift (0 : I → ℝ) = 0 from rfl] using h

def affine (B : Matrix J I ℝ) (x : J → ℝ) : MvPolynomial J ℝ →ₐ[ℝ] MvPolynomial I ℝ :=
  MvPolynomial.aeval (fun j => MvPolynomial.C (x j) + ∑ i, MvPolynomial.C (B j i) * MvPolynomial.X i)

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem evaluated (B : Matrix J I ℝ) (x : J → ℝ) (z : I → ℝ) (p : MvPolynomial J ℝ) :
    MvPolynomial.eval z (affine B x p) = MvPolynomial.eval (x + B*ᵥz) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [affine]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, hf, eval_X]
    simp [affine, Matrix.mulVec, dotProduct]

omit [Fintype J] [DecidableEq J] in
/-- All coupling orders at the chosen coarse configuration, before projection
or changing the test. -/
theorem complete (B : Matrix J I ℝ) (x : J → ℝ) (Q : Matrix I I ℝ)
    (sym : Q.IsSymm) (positive : Q.PosSemidef) (T : PowerSeries (MvPolynomial J ℝ)) :
    WilsonMovingGaussianResponse.numerator Q B x T =
      Series.beam (Wick.moment Q) (PowerSeries.map (affine B x).toRingHom T) := by
  ext i
  rw [WilsonMovingGaussianResponse.numerator, coeff_mk, coeff_beam, PowerSeries.coeff_map]
  change _ = Wick.moment Q (affine B x (PowerSeries.coeff i T))
  rw [← gaussian Q sym positive]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun z : I → ℝ =>
    (evaluated B x z (PowerSeries.coeff i T)).symm)

/-- In particular the literal original nonlinear Cacao emitted column is
normalized against the identical structure of Wick moments used by the
independent finite conditional construction. -/
theorem marked (B : Matrix J I ℝ) (x : J → ℝ) (Q : Matrix I I ℝ)
    (sym : Q.IsSymm) (positive : Q.PosDef) (f T : PowerSeries (MvPolynomial J ℝ))
    (hf : Kind f) (p : ℕ) :
    let take := fun U => Series.beam (Wick.moment Q) (PowerSeries.map (affine B x).toRingHom U)
    Through p (WilsonMovingNormalizedBank.view x (growP f T (B*Q*B.transpose) (p+1)) *
      take (Spring f)) (take (T*Spring f)) := by
  dsimp only
  rw [← complete B x Q sym positive.posSemidef, ← complete B x Q sym positive.posSemidef]
  exact WilsonMovingNormalizedBank.numerator B x positive f T hf p

end YM.Integration.WilsonMovingWickCoefficient
end
