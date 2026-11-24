import YM.Integration.WilsonConditionalTaylorWheelKernel
import YM.Integration.WilsonMovingFiniteConditional

/-! Full original finite gaussian evaluated on its literal fluctuating
and external fields, without a change of covariance or background. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelDeposit
open Function Lattice Matrix PowerSeries FormalBulk08 FormalBulk08.Orb FormalBulk08.Jets FormalBulk08.Series
open Stationary Wick WilsonCoeffUV WilsonCoeffUV.Blue
open scoped Classical BigOperators Matrix
variable {I Y:Type} [Fintype I] [Fintype Y] [DecidableEq I] [DecidableEq Y]

omit [Fintype I] [Fintype Y] [DecidableEq I] [DecidableEq Y] in
theorem separate (z:I→ℝ) (y:Y→ℝ) (p:MvPolynomial (I⊕Y) ℝ):
    MvPolynomial.eval z (MvPolynomial.map (MvPolynomial.eval y) (emer I Y p))=
      MvPolynomial.eval (Sum.elim z y) p:=by
  induction p using MvPolynomial.induction_on with
  | C a => simp [emer]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,hp]
    congr 1
    cases i <;> simp [emer]

omit [Fintype Y] [DecidableEq Y] in
theorem affine (y:Y→ℝ) (p:MvPolynomial (I⊕Y) ℝ):
    MvPolynomial.map (MvPolynomial.eval y) (emer I Y p)=
      WilsonMovingWickCoefficient.affine (WilsonMovingFiniteConditional.lift Y I) (Sum.elim 0 y) p:=by
  apply MvPolynomial.funext
  intro z
  rw [separate,WilsonMovingWickCoefficient.evaluated]
  have h:Sum.elim z y=Sum.elim (0:I→ℝ) y+WilsonMovingFiniteConditional.lift Y I *ᵥ z:=by
    funext j
    cases j <;> simp [WilsonMovingFiniteConditional.lift,Matrix.mulVec,dotProduct]
  rw [h]

omit [DecidableEq Y] in
theorem paid (D:Saddle ℝ I) (y:Y→ℝ) (T:Pap (I⊕Y)):
    glimpse y (Blue.Wick Y D.q T)=WilsonConditionalTaylorWick.contract
      (WilsonMovingFiniteConditional.lift Y I) (Sum.elim 0 y) D.q T:=by
  rw [WilsonConditionalTaylorWheelHeat.full]
  let H:Hull I Y:=⟨D,0,0⟩
  rw [WilsonMovingIndependentWick.covariance H]
  ext e
  rw [coeff_beam,WilsonMovingIndependentWick.observe,coeff_map,coeff_map,
    WilsonConditionalTaylorWick.contract,coeff_beam,coeff_map]
  exact congrArg (Wick.moment D.q) (affine y (coeff e T))

end YM.Integration.WilsonConditionalTaylorWheelDeposit
end

