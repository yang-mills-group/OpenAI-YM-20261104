import YM.Integration.WilsonMovingWickCoefficient
import YM.Integration.WilsonConditionalTaylorNormalizedOrder

/-! At the exact tested order the normalized emitted quantity is computed
by the genuine Wick moment of the signed numerator divided by the genuine
Wick moment of the same unmarked nonlinear action. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWick

open Finset PowerSeries Matrix FormalBulk08 FormalBulk08.Series MSbar MSbar.Cacao MSbar.Bakery
open WilsonMovingNormalizedBank
open scoped Classical BigOperators Matrix

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (B : Matrix J I ℝ) (x : View J) (Q : Matrix I I ℝ)

def contract (T : PowerSeries (MvPolynomial J ℝ)) : PowerSeries ℝ :=
  Series.beam (Wick.moment Q) (PowerSeries.map (WilsonMovingWickCoefficient.affine B x).toRingHom T)

def quotient (f T : PowerSeries (MvPolynomial J ℝ)) : PowerSeries ℝ :=
  contract B x Q (T*Spring f) * PowerSeries.invOfUnit (contract B x Q (Spring f)) 1

theorem response (sym : Q.IsSymm) (pos : Q.PosDef) (f T : PowerSeries (MvPolynomial J ℝ))
    (origin : Kind f) (p : ℕ) :
    Through p (view x (growP f T (B*Q*B.transpose) (p+1))) (quotient B x Q f T) := by
  let z:=contract B x Q (Spring f)
  have one : PowerSeries.coeff 0 z=1 := by
    change PowerSeries.coeff 0 (Series.beam _ _)=1
    rw [←WilsonMovingWickCoefficient.complete B x Q sym pos.posSemidef (Spring f)]
    exact WilsonMovingGaussianResponse.first Q B x (Spring f) (covers origin)
  have normalized : z * PowerSeries.invOfUnit z 1=1 := PowerSeries.mul_invOfUnit _ _ (by
    rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,one]; rfl)
  have eqn:=WilsonMovingWickCoefficient.marked B x Q sym pos f T origin p
  change Through p (view x (growP f T (B*Q*B.transpose) (p+1))*z) (contract B x Q (T*Spring f)) at eqn
  have bought:=eqn.mul (Through.exact_eq (PowerSeries.invOfUnit z 1) p)
  rwa [mul_assoc,normalized,mul_one] at bought

theorem finite (sym : Q.IsSymm) (pos : Q.PosDef) (f T : PowerSeries (MvPolynomial J ℝ))
    (origin : Kind f) (p : ℕ) (g : ℝ) :
    taste p (view x (growP f T (B*Q*B.transpose) (p+1))) g=taste p (quotient B x Q f T) g := by
  unfold taste
  apply Finset.sum_congr rfl
  intro i hi
  rw [response B x Q sym pos f T origin p i (Nat.lt_succ_iff.mp (mem_range.mp hi))]

end YM.Integration.WilsonConditionalTaylorWick
end

