import YM.Integration.WilsonConditionalTaylorWheelBare
import YM.Integration.MSFixedRatioSaddleWick

/-! The upper winding heat operator and the complete independent FVA2
Gaussian integrate literally the same joint polynomial, leaving *all*
external coordinates free. This includes the unnormalized interacting
numerator and vacuum denominator at an arbitrary external field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelHeat
open PowerSeries Matrix FormalBulk08 FormalBulk08.Series FormalBulk08.Orb FormalBulk08.Wick
open WilsonCoeffUV WilsonCoeffUV.Blue Comparison.RG02 Cumulants Next.Rank PhysicalNext.WeightedGaussianMarginal45C.Issue
open scoped Classical BigOperators Matrix
variable {I Y:Type} [Fintype I] [Fintype Y] [DecidableEq I]

omit [Fintype Y] in
private theorem covariance (D:Saddle ℝ I) : fillSlots Y D.q=aqua (I:=Y) D:=by
  ext i j;cases i<;>cases j<;>rfl

theorem full (D:Saddle ℝ I) (T:Pap (I⊕Y)):
    Blue.Wick Y D.q T=beam (variation D Y).call (PowerSeries.map (emer I Y).toRingEquiv.toRingHom T):=by
  rw [moment_aqua,FormalBulk08.Wick.rack_finish]
  apply PowerSeries.ext
  intro e
  simp only [Blue.Wick,projectZero,PowerSeries.coeff_map,Blue.fullB,Blue.blur,overlay_apply,coeff_beam]
  change aftEval I Y (glaze (fillSlots Y D.q) (coeff e T))=aftEval I Y (FormalBulk08.Wick.hearth (aqua D) (coeff e T))
  rw [covariance,MSFixedRatioSaddleWick.polynomial]
  ext i j
  exact aqua_symm D j i

theorem observed (D:Saddle ℝ I) (y:Y→ℝ) (T:Pap (I⊕Y)) (e:ℕ):
    (MvPolynomial.eval y (coeff e (Blue.Wick Y D.q T)):ℂ)=
      Cloud.wick D.q (by ext i j;exact D.ok j i) 0
        (MvPolynomial.map Complex.ofRealHom (MvPolynomial.map (MvPolynomial.eval y)
          (coeff e (PowerSeries.map (emer I Y).toRingEquiv.toRingHom T)))):=by
  rw [full]
  exact (MSFixedRatioSaddleWick.coefficient D y _ e).symm

end YM.Integration.WilsonConditionalTaylorWheelHeat
end

