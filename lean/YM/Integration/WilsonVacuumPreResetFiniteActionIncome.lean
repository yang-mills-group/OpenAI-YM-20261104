import YM.Integration.WilsonVacuumPreResetFiniteCoefficientMass
import YM.Integration.MSFixedRatioSaddleWick
import YM.Next.RANK.Guard

/-! The full Gaussian weight invoice from the actual signed incoming action. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteActionIncome
open Function Finset PowerSeries FormalBulk08 FormalBulk08.Orb FormalBulk08.Wick FormalBulk08.Series
open Comparison.RG02 Comparison.RG02.Cumulants Next.Rank PhysicalNext.WeightedGaussianMarginal45C.Issue
open scoped Classical BigOperators


variable {U I:Type}

private def testAt (B:I→ℝ):
    MvPolynomial U (MvPolynomial I ℝ) →+* MvPolynomial U ℂ:=
  (MvPolynomial.map Complex.ofRealHom).comp (MvPolynomial.map (MvPolynomial.eval B))

def powers (U:Type)(A:ℝ)(e:ℕ):ℝ:=
  ∑k∈range (e+1),Rise.coin (coeff k (PowerSeries.exp (MvPolynomial U ℂ))) * ((e+1:ℝ)*(1+A))^k

def gross (B:I→ℝ)(P Q:Orb.Ink U I)(n:ℕ):ℝ:=
  ∑i∈range (n+1),(Rise.coin (WilsonVacuumPreResetFiniteLogBudget.polynomial B Q i)+
    Rise.coin (WilsonVacuumPreResetFiniteLogBudget.polynomial B P i))

def changed (B:I→ℝ)(P:Orb.Ink U I)(n:ℕ):ℝ:=
  ∑i∈range (n+1),Rise.coin (WilsonVacuumPreResetFiniteLogBudget.polynomial B P i)

def cofactor (M:ℝ)(B:I→ℝ)(A:ℝ)(P:Orb.Ink U I)(n:ℕ):ℝ:=
  ∑i∈range (n+1),powers U A i * Common.priced M (WilsonVacuumPreResetFiniteLogBudget.polynomial B P i).totalDegree

/-- A single signed difference before the finite interacting exponential
pays the entire weight change, with its original Gaussian moment factor. -/
theorem weight (M:ℝ)(hm:1≤M)(B:I→ℝ)(P Q:Orb.Ink U I)(zp:coeff 0 P=0)(zq:coeff 0 Q=0)(n:ℕ):
    ∑i∈range (n+1),WilsonVacuumPreResetFiniteLogBudget.fee M B (expan Q-expan P) i ≤
      cofactor M B (gross B P Q n) (expan Q-expan P) n * changed B (Q-P) n:=by
  let t:=testAt (U:=U) B
  let f:=PowerSeries.map t Q
  let g:=PowerSeries.map t P
  let A:=gross B P Q n
  let D:=changed B (Q-P) n
  have cf (T:Orb.Ink U I) (i:ℕ):coeff i (PowerSeries.map t T)=WilsonVacuumPreResetFiniteLogBudget.polynomial B T i:=coeff_map _ _ _
  have hf:coeff 0 f=0:=by rw [show coeff 0 f=t (coeff 0 Q) from coeff_map _ _ _,zq,map_zero]
  have hg:coeff 0 g=0:=by rw [show coeff 0 g=t (coeff 0 P) from coeff_map _ _ _,zp,map_zero]
  have both(t':ℕ)(ht:t'≤n):Rise.coin (coeff t' f)+Rise.coin (coeff t' g) ≤A:=by
    rw [show coeff t' f=_ from cf Q t',show coeff t' g=_ from cf P t']
    exact single_le_sum (fun i _=>add_nonneg (Rise.sign _ _ zero_le_one) (Rise.sign _ _ zero_le_one)) (mem_range.mpr (by omega))
  have slope(i:ℕ)(hi:i≤n):Rise.coin (coeff i (f-g))≤D:=by
    have eq:f-g=PowerSeries.map t (Q-P):=(map_sub ..).symm
    rw [eq,cf]
    exact single_le_sum (fun i _=>Rise.sign _ _ zero_le_one) (mem_range.mpr (by omega))
  have ha:0≤A:=(add_nonneg (Rise.sign _ _ zero_le_one) (Rise.sign _ _ zero_le_one)).trans (both 0 (Nat.zero_le _))
  have hd:0≤D:=(Rise.sign _ _ zero_le_one).trans (slope 0 (Nat.zero_le _))
  have weights:PowerSeries.map t (expan Q-expan P)=expan f-expan g:=by rw [map_sub,map_expan t zq,map_expan t zp]
  unfold cofactor;rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have le:=Nat.lt_succ_iff.mp (mem_range.mp hi)
  have invoice:=WilsonVacuumPreResetFiniteCoefficientMass.real_weight (n:=i) hf hg A D ha hd
    (fun k hk=>(le_add_of_nonneg_right (Rise.sign _ _ zero_le_one)).trans (both k (hk.trans le)))
    (fun k hk=>(le_add_of_nonneg_left (Rise.sign _ _ zero_le_one)).trans (both k (hk.trans le)))
    (fun k hk=>slope k (hk.trans le))
  rw [←weights,cf] at invoice
  let w:=WilsonVacuumPreResetFiniteLogBudget.polynomial B (expan Q-expan P) i
  have rent:0≤Common.priced M w.totalDegree:=by unfold Common.priced;positivity
  calc
    _≤(powers U A i*D)*Common.priced M w.totalDegree:=mul_le_mul_of_nonneg_right invoice rent
    _= _:=by ring

end YM.Integration.WilsonVacuumPreResetFiniteActionIncome
end
