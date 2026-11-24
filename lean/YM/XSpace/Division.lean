import YM.XSpace.Jets
/-! # Taking out g^l from a polynomial in slots of first valuation -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Formal
open Function Set Filter MeasureTheory MvPolynomial
open scoped Topology InnerProductSpace BigOperators ContDiff Classical
variable {ι V E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (b : Module.Basis ι ℝ E)

lemma jet_zero {f : E → ℂ} : PowerSeries.coeff 0 (JetC b f)=C (f 0) := by
  apply using_test b; intro A; rw [jet_value]; simp [test]

def combine (F : V → E → ℂ) (P : MvPolynomial V ℂ) (x : E) := aeval (fun i=>F i x) P

theorem lush (F : V → E → ℂ) (hF : ∀ i, ContDiffAt ℝ ⊤ (F i) 0) (P : MvPolynomial V ℂ) : ContDiffAt ℝ ⊤ (combine F P) 0 := by
  induction P using induction_on with
  | C a=> rw [show combine F (C a)=fun _=>a from _root_.funext fun i=>by simp [combine]]; exact contDiffAt_const
  | add p q h g => rw [show combine F (p+q)=combine F p+combine F q from _root_.funext fun i=>map_add ..]; exact h.add g
  | mul_X p j h=> rw [show combine F (p*X j)=combine F p*F j from _root_.funext fun i=>by simp [combine]]; exact h.mul (hF j)

-- `algebraMap ℂ` might not have desired PS instance (use eval₂).
lemma jet_combine (F : V → E → ℂ) (hF : ∀ i, ContDiffAt ℝ ⊤ (F i) 0) (P : MvPolynomial V ℂ) :
    JetC b (combine F P) = eval₂Hom (PowerSeries.C.comp C) (fun i=>JetC b (F i)) P := by
  induction P using induction_on with
  | C a=> rw [show combine F (C a)=fun _=>a from _root_.funext fun i=>by simp [combine]]; rw [jet_C]; simp
  | add p q h g=>
    rw [show combine F (p+q)=combine F p+combine F q from _root_.funext fun i=>map_add .., jet_add b (lush F hF _) (lush F hF _), h,g,map_add]
  | mul_X p j h=>
    rw [show combine F (p*X j)=combine F p*F j from _root_.funext fun i=>by simp [combine], jet_mul b (lush F hF _) (hF _),h,map_mul,eval₂Hom_X']

variable {S : Type*} [CommRing S]

def pullOut (k : ℕ) (p : PowerSeries S) : PowerSeries S := PowerSeries.mk fun j=> PowerSeries.coeff (j+k) p

@[simp] lemma reabsorb (p : PowerSeries S) (k : ℕ) : pullOut k (p*PowerSeries.X^k)= p := by
  ext n; simp [pullOut,PowerSeries.coeff_mul_X_pow]
lemma reorder (p : PowerSeries S) (k : ℕ) (hp : PowerSeries.X^k ∣ p) :
    p = pullOut k p*PowerSeries.X^k := by obtain ⟨v,rfl⟩:=hp; rw [mul_comm _ v,reabsorb]
lemma given_zero (p : PowerSeries S) (hp : PowerSeries.coeff 0 p = 0) : p=pullOut 1 p* PowerSeries.X := by
  convert reorder p 1 ?_ using 1
  · rw [pow_one]
  rw [PowerSeries.X_pow_dvd_iff]; intro i hi
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi) ▸ hp

def count {V : Type*} (e : V →₀ ℕ) := e.sum fun _ n=> n

section polynomial
variable (m : ℂ →+* S) (F : V → PowerSeries S) (hF : ∀ i, PowerSeries.coeff 0 (F i) = 0)
include hF
lemma pull_mono (e : V→₀ ℕ) (a : ℂ) :
    eval₂Hom (PowerSeries.C.comp m) F (monomial e a) = eval₂Hom (PowerSeries.C.comp m) (fun i=>pullOut 1 (F i)) (monomial e a) * PowerSeries.X^count e := by
  rw [MvPolynomial.monomial_eq]; simp only [Finsupp.prod,_root_.map_mul,eval₂Hom_C,_root_.map_prod,map_pow,eval₂Hom_X', mul_assoc]
  congr 1
  conv_lhs =>
    arg 2; intro x
    rw [given_zero (F x) (hF x), mul_pow]
  simp only [Finset.prod_mul_distrib,count,Finsupp.sum,Finset.prod_pow_eq_pow_sum]

lemma pull_div (p : MvPolynomial V ℂ) (k : ℕ) (h : ∀ i∈p.support,k ≤ count i) :
    PowerSeries.X^k ∣ eval₂Hom (PowerSeries.C.comp m) F p := by
  rw [p.as_sum] -- inspect
  rw [_root_.map_sum]; refine Finset.dvd_sum fun i hi=>?_
  rw [pull_mono m F hF]; exact dvd_mul_of_dvd_right (pow_dvd_pow _ (h i hi)) _
end polynomial

def homogeneousPart' (p : MvPolynomial V ℂ) (k : ℕ) := ∑ i∈p.support, if count i=k then monomial i (coeff i p) else 0

lemma pull_read (m : ℂ →+* S) (F : V→PowerSeries S) (hF : ∀ i, PowerSeries.coeff 0 (F i)=0)
    (p : MvPolynomial V ℂ) (k : ℕ) (h : ∀ i∈p.support, k ≤ count i) :
    PowerSeries.constantCoeff (pullOut k (eval₂Hom (PowerSeries.C.comp m) F p))=
    eval₂Hom m (fun i=>PowerSeries.coeff 1 (F i)) (homogeneousPart' p k) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, pullOut, PowerSeries.coeff_mk,zero_add]
  conv_lhs=>rw [p.as_sum]
  unfold homogeneousPart'; simp only [map_sum]; apply Finset.sum_congr rfl; intro i hi
  rw [pull_mono m F hF,PowerSeries.coeff_mul_X_pow']
  by_cases he : count i=k
  · rw [he]; simp only [le_refl, ↓reduceIte, Nat.sub_self]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; rw [monomial_eq]; simp only [map_mul, Finsupp.prod,_root_.map_prod,map_pow,eval₂Hom_C,RingHom.comp_apply,eval₂Hom_X']; rw [PowerSeries.constantCoeff_C]; simp only [pullOut,← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,zero_add] -- inspect
  rw [if_neg (show ¬ count i≤ k by have := h i hi; omega),if_neg he,map_zero]
lemma pull_read' (m : ℂ →+* S) (F : V→PowerSeries S) (hF : ∀ i, PowerSeries.coeff 0 (F i)=0)
    (p : MvPolynomial V ℂ) (k : ℕ) (h : ∀ i∈p.support, k ≤ count i) :
    PowerSeries.coeff k (eval₂Hom (PowerSeries.C.comp m) F p)=
    eval₂Hom m (fun i=>PowerSeries.coeff 1 (F i)) (homogeneousPart' p k) := by
  have he:=pull_read m F hF p k h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, pullOut, PowerSeries.coeff_mk,zero_add] at he; exact he
end YM.XSpace.Formal
