import YM.MatchingLedger.Books.Almanac
import YM.MatchingLedger.Books.Fountain

/-!
# Finite-regulator prediction for normalized inserted moments, and its SD equation

Every rank, overlap pays. Convolution with formal inverse of the **full vacuum series**
means these are standard predictions before taking any logarithm for connected pieces
or projection in grade. Uses `pour` (Gaussian integral with inverse of genuine quadratic,
centered then mean-shift, specified externally).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Books.FPS
open Function Filter Matrix Finset PowerSeries
open scoped BigOperators Classical
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (V : ℕ → Poly ι) (T : Fountain (V 0))

-- Array of inserting *P*
def numer (n : ℕ) : Prediction ι:= T.pour.comp (LinearMap.mul ℝ _ (thermal V n))
def counted (P : Poly ι): PowerSeries ℝ:= mk (fun n=> numer V T n P)
def denominator : PowerSeries ℝ:= counted V T 1
def inverse (n : ℕ) := coeff n (denominator V T)⁻¹

def report (n : ℕ) : Prediction ι:= ∑ i∈ antidiagonal n, inverse V T i.1 • (numer V T i.2)
lemma refresh (n : ℕ)(P : Poly ι) : report V T n P= coeff n ((denominator V T)⁻¹ * counted V T P):= by unfold report; rw [LinearMap.sum_apply, coeff_mul]; apply Finset.sum_congr rfl; intro i _; rw [counted,coeff_mk]; rfl
lemma den_zero : constantCoeff (denominator V T)=1:= by
  rw [← coeff_zero_eq_constantCoeff_apply]; rw [denominator,counted,coeff_mk]; change T.pour (thermal V 0*1)=1; rw [thermal_one,one_mul,T.pour_one]
lemma returns_unit (n : ℕ) : report V T n 1=if n=0 then 1 else 0 := by rw [refresh,← denominator,PowerSeries.inv_mul_cancel _ (by rw [den_zero]; norm_num),coeff_one n]
lemma poured (P : Poly ι) : report V T 0 P=T.pour P:=by
  rw [refresh, coeff_zero_eq_constantCoeff_apply,map_mul,constantCoeff_inv,den_zero,inv_one, one_mul]; rw [← coeff_zero_eq_constantCoeff_apply,counted,coeff_mk]; change T.pour (thermal V 0*P)=_; rw [thermal_one,one_mul]

abbrev slope {ι:Type*} (V : ℕ → Poly ι)(j : ι) := fun k=> MvPolynomial.pderiv j (higher V k)
abbrev base {ι:Type*} (V : ℕ → Poly ι)(j : ι) := MvPolynomial.pderiv j (V 0)

def force {ι:Type*} (V : ℕ → Poly ι)(j : ι) (P : Poly ι) := base V j * P - MvPolynomial.pderiv j P

-- antidiagonal index first chosen as PREVIOUS order, second consumed positive vertex.
omit [DecidableEq ι] [Fintype ι] in
private lemma reverse_current (j:ι) (n:ℕ) : MvPolynomial.pderiv j (thermal V n) = -∑ i∈antidiagonal n,slope V j i.2 * thermal V i.1:=by
  rw [current]; congr 1; apply Eq.symm; exact @Finset.Nat.sum_antidiagonal_swap _ _ n (fun i=> slope V j i.1*thermal V i.2) -- check
lemma numer_sd (j:ι)(n : ℕ)(P : Poly ι) : numer V T n (force V j P)= -∑ i∈antidiagonal n, numer V T i.1 (slope V j i.2 * P):=by
  let A:=numer V T n; let B:=thermal V n; let c:= base V j; let v:= ∑ i∈antidiagonal n, slope V j i.2*thermal V i.1
  have hz: T.pour (B*(c*P))= T.pour (B*MvPolynomial.pderiv j P)+T.pour ((-v)*P):=by
     rw [show B*(c*P)=c*(B*P) from by ring]
     rw [show T.pour (c*_) = _ from T.works (B*P) j,MvPolynomial.pderiv_mul,show MvPolynomial.pderiv j B=-v from reverse_current V j n,map_add,add_comm]
  rw [force]; change T.pour (B*(c*P - _)) = _; rw [mul_sub,map_sub,hz,add_comm (T.pour (B*_)),add_sub_cancel_right,neg_mul,map_neg]; unfold v; simp_rw [Finset.sum_mul,map_sum]; congr 1
  exact sum_congr rfl fun i _=> by unfold numer; change T.pour ((_*_)*_)=T.pour (_*(_*_)); ring_nf
lemma report_sd (j:ι)(n:ℕ)(P:Poly ι): report V T n (force V j P)= -∑ i∈antidiagonal n,report V T i.1 (slope V j i.2 * P):=by
  simp_rw [report, LinearMap.sum_apply, LinearMap.smul_apply, numer_sd, smul_eq_mul,mul_neg,Finset.mul_sum,Finset.sum_neg_distrib]
  apply congr_arg Neg.neg
  exact (triple (fun a b c=> inverse V T a*numer V T b (slope V j c * P)) n).symm
end YM.MatchingLedger.Books.FPS
