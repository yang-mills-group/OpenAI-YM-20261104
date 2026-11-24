import YM.FormalBulk08.Series.Stencil

/-!
Normalized local Gaussian algebra. Leg algebra `Glyphs R V`; covariance includes any
zero rows/columns. `R` can include other letters not subject to integration.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series
open scoped Classical BigOperators
open MvPolynomial
variable {R S : Type*} {V : Type*} [CommRing R] [CommRing S]

lemma alphabet_swap (i j : V) (p : Glyphs R V) : pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
   by_cases h:i=j
   · rw [h]
   ext1 n; simp only [coeff_pderiv, Finsupp.add_apply]
   simp [h, add_right_comm n, mul_right_comm]

lemma pderiv_degree (i : V) (p : Glyphs R V) : (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
   rw [totalDegree]; apply Finset.sup_le; intro b hb
   rw [mem_support_iff,coeff_pderiv] at hb
   have he := le_totalDegree (mem_support_iff.mpr (left_ne_zero_of_mul hb))
   rw [Finsupp.sum_add_index' (fun _=>rfl) (fun _ _ _=>rfl)] at he
   simp at he; omega

variable [Fintype V] [Algebra ℚ R] (q : V → V → R)
def halve (r : R) := algebraMap ℚ R (1/2) * r
lemma half_twice (r : R) : halve r + halve r = r := by unfold halve; rw [←add_mul, ←map_add, show ((1:ℚ)/2)+1/2=1 by norm_num,map_one,one_mul]

/-- Half of the Gaussian Laplacian. -/
def press : Glyphs R V →ₗ[R] Glyphs R V := ∑ i, ∑ j, halve (q i j) • ((pderiv i).toLinearMap.comp (pderiv j).toLinearMap)
lemma press_eq (p : Glyphs R V) : press q p = ∑ i,∑ j, (C (halve (q i j)) * pderiv i (pderiv j p)) := by simp [press,MvPolynomial.smul_eq_C_mul]
lemma press_degree (p : Glyphs R V) : (press q p).totalDegree ≤ p.totalDegree - 2 := by
   rw [press_eq]; refine totalDegree_finsetSum_le (fun i _=> totalDegree_finsetSum_le (fun j _=> (totalDegree_mul ..).trans ?_))
   rw [totalDegree_C]; have hi := pderiv_degree i (pderiv j p); have hj:= pderiv_degree j p; omega
lemma press_inert (p : Glyphs R V) (hp : p.totalDegree < 2) : press q p=0 := by
   rw [press_eq]; refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _=> ?_
   have hh : (pderiv j p).totalDegree=0 := by have := pderiv_degree j p; omega
   rw [totalDegree_eq_zero_iff_eq_C.mp hh,pderiv_C,mul_zero]
lemma press_nilpotent (p : Glyphs R V) (n : ℕ) (hp : p.totalDegree < 2*n) : (press q ^ n : Module.End R _) p=0 := by
   induction n generalizing p with
   | zero=> omega
   | succ n ih=>
      rcases n with (_|n)
      · rw [pow_one]; exact press_inert q p (by omega)
      rw [pow_succ, Module.End.mul_apply]; apply ih
      have := press_degree q p; omega

lemma press_commutes (i : V) (p : Glyphs R V) : press q (pderiv i p) = pderiv i (press q p) := by
   simp_rw [press_eq,map_sum,pderiv_C_mul]; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _
   congr 1; rw [alphabet_swap k,alphabet_swap j i]

/-- Commutator with coordinate multiplication (normalized Wick). -/
lemma press_mul_X (s : ∀ i j,q i j=q j i) (p : Glyphs R V) (i : V) : press q (X i * p)= X i * press q p + ∑ j,C (q i j) * pderiv j p := by
   have hx (a b:V) : pderiv a (pderiv b (X i * p))=X i*pderiv a (pderiv b p)+(if b=i then pderiv a p else 0)+(if a=i then pderiv b p else 0) := by
     rw [pderiv_mul,map_add,pderiv_mul,pderiv_mul]
     by_cases hb:b=i <;> by_cases ha:a=i <;> simp_all [eq_comm] <;> abel
   rw [press_eq];simp_rw [hx, mul_add, Finset.sum_add_distrib]; rw [add_assoc]
   congr 1
   · rw [press_eq]; simp_rw [Finset.mul_sum, mul_left_comm (C _) (X i)]
   rw [Finset.sum_comm (f:=fun (a b:V) => C (halve (q a b))*(if a=i then pderiv b p else 0))]; simp_rw [mul_ite,mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
   rw [← Finset.sum_add_distrib];apply Finset.sum_congr rfl; intro j _; rw [s j,←add_mul,←_root_.map_add, half_twice]
end YM.FormalBulk08.Wick
