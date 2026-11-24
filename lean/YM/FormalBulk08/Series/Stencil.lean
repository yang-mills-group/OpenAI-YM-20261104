import YM.FormalBulk08.Series.Shade
import Mathlib.Algebra.MvPolynomial.PDeriv
/-!
Formal multivariate polynomial parameter substitution. PowerSeries independent variable
used for g. Letters here are absolute log-link coordinates, not lexical alphabet of
separated fields. Chain rule acts on auxiliary parameter.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Series
open PowerSeries
open scoped BigOperators Classical
variable {K R S : Type*} {V W : Type*} [CommRing K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

abbrev Glyphs (K V : Type*) [CommRing K] := MvPolynomial V K

def insertAt (K : Type*) [CommRing K] [Algebra K R] (f : V → PowerSeries R) : Glyphs K V →+* PowerSeries R := (MvPolynomial.aeval (R:=K) f).toRingHom
@[simp] theorem insert_X (f : V → PowerSeries R) (i : V) : insertAt K f (MvPolynomial.X i)=f i := by simp [insertAt]
@[simp] theorem insert_C (f : V → PowerSeries R) (r : K) : insertAt K f (MvPolynomial.C r)=PowerSeries.C (algebraMap K R r) := by simp [insertAt] ; exact PowerSeries.algebraMap_apply
lemma insert_chain_start (f : V → PowerSeries R) (g : R →+* PowerSeries S) (hc : ∀ a : K,g (algebraMap K R a)= PowerSeries.C (algebraMap K S a)) : (changeBy g).comp (insertAt K f) = insertAt K (fun i=> changeBy g (f i)) := by
   ext

   all_goals simp [hc]
lemma const_insertAt (f : V → R) : insertAt K (PowerSeries.C ∘ f) = PowerSeries.C.comp (MvPolynomial.aeval f).toRingHom := by
  ext

  all_goals simp
lemma diff_letter [Fintype V] (f : V → PowerSeries R) (d : Derivation K R R) (p : Glyphs K V) :
    shaft d (insertAt K f p) = ∑ i, insertAt K f (MvPolynomial.pderiv i p) * shaft d (f i) := by
   induction p using MvPolynomial.induction_on with
   | C c=> simp
   | add p q hp hq=> simp only [map_add,add_mul,Finset.sum_add_distrib,hp,hq]
   | mul_X p i hi=>
      calc shaft d (insertAt K f (p*MvPolynomial.X i)) = ∑ j, insertAt K f (MvPolynomial.pderiv j p) * insertAt K f (MvPolynomial.X i) * shaft d (f j) + ∑ j, insertAt K f p * insertAt K f (MvPolynomial.pderiv j (MvPolynomial.X i)) * shaft d (f j) := ?_
           _ = _ := by simp only [MvPolynomial.pderiv_mul,map_mul,map_add,add_mul,Finset.sum_add_distrib]
      rw [map_mul,Derivation.leibniz,smul_eq_mul,smul_eq_mul,hi,insert_X,add_comm,Finset.mul_sum];
      congr 1
      · apply Finset.sum_congr rfl; intro _ _; ring
      rw [Finset.sum_eq_single i]; all_goals simp_all [eq_comm]

@[simp] lemma shaft_X (d : Derivation K R R) : shaft d X=0 := by ext1 n; simp only [coeff_shaft, PowerSeries.coeff_X]; split_ifs <;> simp_all
lemma diff_chain [Fintype V] (f : V → PowerSeries R) (d : Derivation K R R) (p : PowerSeries (Glyphs K V)) :
    shaft d (changeBy (insertAt K f) p) = ∑ i, changeBy (insertAt K f) (shaft (MvPolynomial.pderiv i) p) * shaft d (f i) := by
   apply Through.top; intro n
   have h : Through n (shaft d (changeBy (insertAt K f) p)) (shaft d (∑ j∈Finset.range (n+1), insertAt K f (coeff j p)*X^j)) := beam_through _ (liquid _ _ n)
   apply h.trans; refine Through.trans ?_ (Through.finsetSum (n:=n) (s:=Finset.univ) (fun i _=> ((liquid _ (shaft (MvPolynomial.pderiv i) p) n).symm).mul (Through.exact_eq (shaft d (f i)) n)))
   simp_rw [map_sum, Derivation.leibniz, Derivation.leibniz_pow, shaft_X,smul_zero,zero_add,diff_letter f d, smul_eq_mul,Finset.sum_mul,Finset.mul_sum,coeff_shaft]
   rw [Finset.sum_comm]; apply Through.finsetSum;intro i _;apply Through.finsetSum;intro j _; rw [← mul_assoc,mul_comm (_ ^ j)]
end YM.FormalBulk08.Series
