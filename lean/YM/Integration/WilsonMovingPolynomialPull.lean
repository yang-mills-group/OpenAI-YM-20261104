import YM.Integration.WilsonMovingTaylorConvention
import YM.MSbar.Rolling.Light

/-! Evaluating an incoming finite polynomial before its specified linear
change of coordinates, at every coupling degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingPolynomialPull
open Filter Function PowerSeries Matrix FormalBulk08 Jets Series MSbar.Rolling
open scoped Classical Topology Matrix
variable {I J R : Type}

def place (s : I → J) (T : PowerSeries (MvPolynomial I ℝ)) := PowerSeries.map (MvPolynomial.rename s).toRingHom T

theorem placed (s : I → J) (T : PowerSeries (MvPolynomial I ℝ)) (x : Rays J) :
    glimpse x (place s T) = glimpse (x ∘ s) T := by
  ext n
  rw [glimpse_coeff, place, PowerSeries.coeff_map, glimpse_coeff]
  change MvPolynomial.aeval x (MvPolynomial.rename s (coeff n T)) =
    MvPolynomial.aeval (x ∘ s) (coeff n T)
  rw [MvPolynomial.aeval_rename]

theorem linear [Fintype I] [Fintype J] (B : Matrix J I ℝ) (T : PowerSeries (MvPolynomial J ℝ)) (x : Rays I) :
    glimpse x (PowerSeries.map (rail B).toRingHom T) = glimpse (B *ᵥ x) T := by
  ext n
  rw [glimpse_coeff, PowerSeries.coeff_map, glimpse_coeff]
  exact congrFun (clearL B x) (coeff n T)

theorem detected {T U : PowerSeries (MvPolynomial I ℝ)} (h : ∀ x, glimpse x T=glimpse x U) : T=U := by
  apply PowerSeries.ext
  intro n
  apply MvPolynomial.funext
  intro x
  exact congrArg (coeff n) (h x)

theorem germ [Fintype I] (f g : Rays I→ℝ) (h : f=ᶠ[𝓝 0] g) :
    Jets.paste f=Jets.paste g := by
  apply PowerSeries.ext
  intro n
  rw [← WilsonMovingTaylorConvention.coefficient, ← WilsonMovingTaylorConvention.coefficient]
  simp only [WilsonMovingTaylorConvention.tensor, Tensor.coeff, (h.iteratedFDeriv ℝ n).self_of_nhds]

theorem strip [CommRing R] (a b c d : PowerSeries R) (h : X^2*a = X^2*b-c+X^2*d) :
    a = b - Jets.afterX c 2 + d := by
  apply PowerSeries.ext
  intro n
  have v := congrArg (coeff (2+n)) h
  simpa [coeff_X_pow_mul', Jets.after_one] using v

end YM.Integration.WilsonMovingPolynomialPull
end
