import YM.Integration.WilsonMovingGaussianResponse
import YM.MSbar.Cacao.Coda

/-! The unrestricted finite posterior's normalized emitted rows have the
registered homogeneous Gaussian numerator and its own unmarked denominator.
The nonlinear logarithmic construction respects a coupling shift through its
full booked order, including a genuinely nonconstant zeroth incoming row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingNormalizedBank
open Function PowerSeries Matrix MeasureTheory FormalBulk08 Series MSbar.Cacao
open Further.GaussianScalar Next.SectorChange
open scoped Classical Matrix BigOperators
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (B : Matrix J I ℝ) (x : View J) {Q : Matrix I I ℝ} (positive : Q.PosDef)
    (f T : PowerSeries (MvPolynomial J ℝ)) (origin : Kind f) (p : ℕ)

def view (x : View J) := PowerSeries.map (MvPolynomial.eval x)

include positive origin

/-- Actual Cacao vacuum, evaluated at the original outgoing field. -/
theorem vacuum :
    view x (Spring (confect (B*Q*B.transpose) f)) =
      WilsonMovingGaussianResponse.numerator Q B x (Spring f) := by
  ext n
  have h := goodie B x positive origin n
  simpa only [view,PowerSeries.coeff_map,WilsonMovingGaussianResponse.numerator,
    PowerSeries.coeff_mk,WilsonMovingGaussianGeometry.law] using h

/-- Actual Cacao marked column at all orders through p. There is no
assumption on the degree-zero coefficient of the input T. -/
theorem numerator :
    Through p (view x (growP f T (B*Q*B.transpose) (p+1)) *
      WilsonMovingGaussianResponse.numerator Q B x (Spring f))
      (WilsonMovingGaussianResponse.numerator Q B x (T*Spring f)) := by
  rw [←vacuum B x positive f origin]
  intro n hn
  have h := aromaEval B x positive f T (r:=p+1) origin (n:=n) (by omega)
  simpa only [view,←_root_.map_mul,PowerSeries.coeff_map,WilsonMovingGaussianResponse.numerator,
    PowerSeries.coeff_mk,WilsonMovingGaussianGeometry.law] using h

/-- In the actual original Cacao bank the price of multiplying a general
input by X at one extra order is exactly one power of the coupling. -/
theorem restored :
    Through (p+1) (view x (growP f (X*T) (B*Q*B.transpose) ((p+1)+1)))
      (X*view x (growP f T (B*Q*B.transpose) (p+1))) := by
  exact WilsonMovingGaussianResponse.response Q B x (Spring f) T (covers origin) p _ _
    (numerator B x positive f T origin p) (numerator B x positive f (X*T) origin (p+1))

end YM.Integration.WilsonMovingNormalizedBank
