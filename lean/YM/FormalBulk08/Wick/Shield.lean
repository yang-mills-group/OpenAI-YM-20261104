import YM.FormalBulk08.Wick.Petal

/-! Normalized algebraic saddle. Wick prescription at finite volume using precision
of rescaled logarithms. Can carry symbol parameters in R. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series PowerSeries Matrix
open scoped BigOperators
variable {R S V : Type*} [CommRing R] [Algebra ℚ R] [DecidableEq V] [Fintype V]

structure Saddle (R V : Type*) [CommRing R] [Fintype V] [DecidableEq V] where
   q : Matrix V V R
   P : Matrix V V R
   ok : ∀ i j,q i j=q j i
   valid : ∀ i j,P i j=P j i
   inv : P*q=1
namespace Saddle
variable (T : Saddle R V)
omit [Algebra ℚ R] in
lemma inv_column (i j:V) : ∑ k, T.P i k*T.q k j = if i=j then 1 else 0 := by rw [← Matrix.mul_apply,T.inv,Matrix.one_apply]
def base : Glyphs R V:= -∑ i,∑ j,MvPolynomial.C (halve (T.P i j))*MvPolynomial.X i*MvPolynomial.X j

theorem d_base (j : V) : MvPolynomial.pderiv j T.base= -∑ i,MvPolynomial.C (T.P j i)*MvPolynomial.X i := by
   have h (u v : V): MvPolynomial.pderiv j (MvPolynomial.C (halve (T.P u v))*MvPolynomial.X u*MvPolynomial.X v)=(if u=j then MvPolynomial.C (halve (T.P u v))*MvPolynomial.X v else 0)+(if v=j then MvPolynomial.C (halve (T.P u v))*MvPolynomial.X u else 0) := by
     rw [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C_mul]
     by_cases hu:u=j <;> by_cases hv:v=j <;> simp_all
   simp_rw [base,map_neg,map_sum,h,Finset.sum_add_distrib]; congr 1
   rw [Finset.sum_comm];simp_rw [Finset.sum_ite_eq',Finset.mem_univ,if_true]; rw [← Finset.sum_add_distrib];apply Finset.sum_congr rfl; intro i _; rw [T.valid i j,← add_mul,← _root_.map_add, half_twice]

abbrev call : Glyphs R V →ₗ[R] R:=moment T.q
lemma annihilate (i : V) (p : Glyphs R V) : T.call (MvPolynomial.pderiv i p+MvPolynomial.pderiv i T.base * p)=0 := by
   simp_rw [d_base,neg_mul,Finset.sum_mul,mul_assoc,map_add,map_neg,map_sum,MvPolynomial.C_mul', call,map_smul,paired T.q T.ok,smul_eq_mul,Finset.mul_sum]
   rw [Finset.sum_comm]; simp_rw [←mul_assoc,←Finset.sum_mul, T.inv_column,ite_mul,one_mul,zero_mul, Finset.sum_ite_eq, Finset.mem_univ,if_true, add_neg_cancel]

/-- Moment carrying time parameter (for proving divergence invariance). -/
def sweepL (A : Polynomial (Glyphs R V)) := A.sum fun n p=> Polynomial.monomial n (T.call p)
@[simp] lemma sweepL_coeff (A : Polynomial (Glyphs R V)) (n : ℕ) : Polynomial.coeff (T.sweepL A) n=T.call (A.coeff n) := by
  classical
  simp only [sweepL,Polynomial.sum,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial];rw [Finset.sum_eq_single n]; all_goals simp_all

def sweep : Polynomial (Glyphs R V) →ₗ[R] Polynomial R where
   toFun := T.sweepL
   map_add' _ _ := by ext; simp
   map_smul' _ _ := by ext; simp
@[simp] lemma sweep_coeff (A : Polynomial (Glyphs R V)) (n : ℕ) : Polynomial.coeff (T.sweep A) n=T.call (A.coeff n) := T.sweepL_coeff ..
lemma icon (U : PowerSeries (Polynomial (Glyphs R V))) (j : V) : beam T.sweep (shaft (grain j) U+ shaft (grain j) (C (Polynomial.C T.base))*U)=0 := by
   ext n m; simp only [coeff_beam,map_add,shaft_C, coeff_shaft, coeff_C_mul,map_zero,Polynomial.coeff_zero];rw [show grain j (Polynomial.C T.base)=Polynomial.C (MvPolynomial.pderiv j T.base) by ext k; by_cases hk:k=0 <;> simp [Polynomial.coeff_C, hk]] -- ext index
   rw [Polynomial.coeff_add,T.sweep_coeff,T.sweep_coeff,Polynomial.coeff_C_mul,grain_coeff,← map_add]; exact T.annihilate _ _
end Saddle

/-- Derivative in independent homotopy variable. -/
def tint : Derivation R (Polynomial (Glyphs R V)) (Polynomial (Glyphs R V)) := Polynomial.derivative'.restrictScalars R
omit [Algebra ℚ R] [DecidableEq V] [Fintype V] in
lemma tint_apply (p : Polynomial (Glyphs R V)) : tint p=Polynomial.derivative p := rfl
lemma shaft_tint (T : Saddle R V) (F : PowerSeries (Polynomial (Glyphs R V))) : shaft Polynomial.derivative' (beam T.sweep F) = beam T.sweep (shaft tint F) := by
   ext1 n; simp only [coeff_shaft,coeff_beam,tint_apply]; change Polynomial.derivative _= _; ext m
   simp only [Polynomial.coeff_derivative,Saddle.sweep_coeff,←Nat.cast_succ];
   rw [mul_comm _ (Nat.cast (m+1)),←nsmul_eq_mul];
   rw [mul_comm _ (Nat.cast m.succ),← nsmul_eq_mul,map_nsmul]
end YM.FormalBulk08.Wick
