import YM.Integration.WilsonMovingGaussianGeometry
import YM.FormalBulk08.Series.Level

/-! A coupling shift removes the constant-field entrance restriction of a
normalized finite Gaussian coefficient bank. Its two numerator sales use
the same measured Gaussian and their own true unmarked denominator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingGaussianResponse
open MeasureTheory PowerSeries FormalBulk08 Series Next.SectorChange
open scoped Matrix Classical BigOperators

section
variable {S : Type*} [CommRing S]

private theorem zeroX (A : PowerSeries S) : coeff 0 (X*A)=0 := by
  rw [coeff_zero_eq_constantCoeff,_root_.map_mul,constantCoeff_X,zero_mul]

private theorem succX (A : PowerSeries S) (n : ℕ) : coeff (n+1) (X*A)=coeff n A := by
  rw [← pow_one (X : PowerSeries S),coeff_X_pow_mul']
  simp

theorem shift {A B : PowerSeries S} {p : ℕ} (old : Through p A B) :
    Through (p+1) (X*A) (X*B) := by
  intro i hi
  cases i with
  | zero => rw [zeroX,zeroX]
  | succ i => rw [succX,succX]; exact old i (by omega)

/-- Division is by a formal unit with constant one. The lower sale at p
already determines the entire new bank to p+1 for one shifted source. -/
theorem divided {Z V P Q : PowerSeries S} {p : ℕ} (unit : coeff 0 Z=1)
    (before : Through p (P*Z) V) (after : Through (p+1) (Q*Z) (X*V)) :
    Through (p+1) Q (X*P) := by
  have actual : Through (p+1) (Q*Z) ((X*P)*Z) := by
    rw [mul_assoc]
    exact after.trans (shift before).symm
  obtain ⟨u,hu⟩ : IsUnit Z := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [←coeff_zero_eq_constantCoeff_apply,unit]
    exact isUnit_one
  have clear : Z * ((u⁻¹ : (PowerSeries S)ˣ) : PowerSeries S)=1 := by rw [←hu,Units.mul_inv]
  have sold := actual.mul (Through.exact_eq ((u⁻¹ : (PowerSeries S)ˣ) : PowerSeries S) (p+1))
  rwa [mul_assoc,clear,mul_one,mul_assoc,clear,mul_one] at sold

end

variable {I J : Type} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ℝ) (P : Matrix J I ℝ) (x : J→ℝ)

/-- The original full covariance and the exact affine mean are kept inside
each coefficient. This is a homogeneous Gaussian numerator. -/
def numerator (T : PowerSeries (MvPolynomial J ℝ)) : PowerSeries ℝ :=
  PowerSeries.mk fun n => ∫ z, MvPolynomial.eval (x+P*ᵥz) (coeff n T) ∂Gaussian.cloud Q

theorem first (T : PowerSeries (MvPolynomial J ℝ)) (one : coeff 0 T=1) :
    coeff 0 (numerator Q P x T)=1 := by
  rw [numerator,coeff_mk,one]
  simp

theorem raised (T : PowerSeries (MvPolynomial J ℝ)) :
    numerator Q P x (X*T)=X*numerator Q P x T := by
  ext n
  cases n with
  | zero => rw [zeroX,numerator,coeff_mk,zeroX]; simp
  | succ n => rw [succX]; simp only [numerator,coeff_mk,succX]

/-- Both signed banks use the unchanged original thermal weight W. The
shifted contribution at any coarse test is one coupling power times the
unshifted bank, including every lower coefficient. -/
theorem response (W T : PowerSeries (MvPolynomial J ℝ)) (one : coeff 0 W=1)
    (p : ℕ) (A B : PowerSeries ℝ)
    (before : Through p (A*numerator Q P x W) (numerator Q P x (T*W)))
    (after : Through (p+1) (B*numerator Q P x W) (numerator Q P x ((X*T)*W))) :
    Through (p+1) B (X*A) := by
  rw [mul_assoc,raised] at after
  exact divided (first Q P x W one) before after

end YM.Integration.WilsonMovingGaussianResponse
