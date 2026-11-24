import YM.Next.RANK.Rise
import YM.FormalOPE.RG10.Routes.Geometry

/-!
# Max-lens polynomial moment costs

Analogue of `Rank.Rise` for sup-cost rather than valuation. May translate to another
polynomial moment without any cost involving field count at unused locations. Does not assume
f(R) has rank two just because its perturbative order is near tree. kinematic distances *on all
legs*, using whatever `Lens` (sum unions etc) is active.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open MvPolynomial Function Finset Next.Rank.Rise
open scoped Topology BigOperators Classical
variable {I : Type*}
abbrev Packet (I : Type*) := MvPolynomial I ℂ
abbrev Letters (I : Type*) := I →₀ ℕ

def fare (m : I → ℝ) (u : ℕ) (q : Letters I) := tip (along m q.support) u
def worth (m : I → ℝ) (u : ℕ) (p : Packet I) := ∑ i∈p.support,fare m u i * ‖coeff i p‖
lemma worth_mono {w v : I → ℝ} (h : w ≤ v) (h' : 0 ≤ w) (u : ℕ) (p : Packet I) :
    worth w u p ≤ worth v u p := sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      (tip_mono (mono_along (le_refl i.support) w v (fun j _ => h j) (h'.trans h)) (along_nn h' _) u) (norm_nonneg _)
lemma fare_mono {w v : I → ℝ} (h : w ≤ v) (h' : 0 ≤ w) (u : ℕ) (p : Letters I) :
    fare w u p ≤ fare v u p := tip_mono (mono_along (le_refl p.support) w v (fun j _ => h j) (h'.trans h)) (along_nn h' _) u

variable {Z : Type*} (I) (m : I → ℝ) (h : 0 ≤ m) (u : ℕ) (p q : Packet I)
variable {I}
include h
lemma fare_pos (a : Letters I) : 0 < fare m u a := tip_pos (along_nn h _) u
lemma fare_one (a : Letters I) : 1 ≤ fare m u a := tip_charge (along_nn h _) u
lemma worth_nonneg : 0 ≤ worth m u p := sum_nonneg fun i _ => mul_nonneg (fare_pos m h u i).le (norm_nonneg _)
lemma worth_order {v : ℕ} (h' : u ≤ v) : worth m u p ≤ worth m v p := sum_le_sum fun _ _ =>
    mul_le_mul_of_nonneg_right (tip_mono_age (along_nn h _) h') (norm_nonneg _)
omit h
lemma worth_monomial (a : Letters I) (c : ℂ) : worth m u (monomial a c) = fare m u a * ‖c‖ := by
  unfold worth; rw [← sum_def (b:=fun i v => fare m u i * ‖v‖)]; exact MvPolynomial.sum_monomial_eq (by simp)
lemma worth_flat : worth m 0 p= coin p := by rw [metal,worth]; simp [fare,tip]
lemma fare_nothing : fare m u 0=1 := by simp [fare]
@[simp] lemma worth_empty : worth m u 0=0 := by simp [worth]
lemma worth_neg : worth m u (-p)=worth m u p := by simp [worth]
@[simp] lemma worth_C (c:ℂ) : worth m u (C c)=‖c‖ := by rw [show C c=(monomial 0 c : Packet I) from rfl,worth_monomial,fare_nothing,one_mul]
@[simp] lemma worth_one : worth m u 1=1 := by rw [← show C 1=(1:Packet I) from map_one _,worth_C,norm_one]
lemma worth_X (i : I) : worth m u (X i)= tip (m i) u := by rw [X,worth_monomial, fare]; simp
lemma worth_smul (r : ℂ) : worth m u (r • p)=‖r‖*worth m u p := by
  unfold worth; by_cases hr : r=0
  · simp [hr]
  rw [show (r • p).support=p.support from ?_,Finset.mul_sum]; swap
  · ext i; rw [mem_support_iff,mem_support_iff,coeff_smul]; simp [hr]
  apply sum_congr rfl; intro i _; rw [coeff_smul, norm_smul]; ring
include h
lemma along_add (i j : Letters I) : along m (i+j).support ≤ max (along m i.support) (along m j.support) := by
  apply along_le _ _ ((along_nn h _).trans (le_max_left ..))
  intro u he; by_cases h' : u∈i.support
  · exact (le_along h' m).trans (le_max_left ..)
  exact (le_along ((mem_union.mp (Finsupp.support_add he)).resolve_left h') m).trans (le_max_right ..)
lemma fare_add (i j : Letters I) : fare m u (i+j) ≤ fare m u i * fare m u j := by
  have he := along_add m h i j
  apply (tip_mono (he.trans <| max_le (le_add_of_nonneg_right (along_nn h _)) (le_add_of_nonneg_left (along_nn h _))) (along_nn h _) u).trans
  exact tip_add (along_nn h _) (along_nn h _) u
lemma worth_add : worth m u (p+q) ≤ worth m u p + worth m u q := by
  let A := p.support ∪ q.support
  have he (p) (hp:MvPolynomial.support p⊆A) : worth m u p = ∑ i∈A,fare m u i *‖coeff i p‖ :=
    sum_subset hp fun i _ hi => by rw [MvPolynomial.notMem_support_iff.mp hi,norm_zero,mul_zero]
  rw [he (p+q) MvPolynomial.support_add,he p subset_union_left,he q subset_union_right,← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_; rw [← mul_add,coeff_add]; exact mul_le_mul_of_nonneg_left (norm_add_le ..) (fare_pos m h u i).le
lemma worth_sub : worth m u (p-q)≤worth m u p + worth m u q := by rw [sub_eq_add_neg,← worth_neg m u q]; exact worth_add m h u p _
lemma worth_sum (s:Finset Z) (f:Z→Packet I) : worth m u (∑ i∈s,f i)≤∑ i∈s,worth m u (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [sum_insert hi,sum_insert hi]; exact (worth_add m h u (f i) _).trans (add_le_add_right ih _)
lemma worth_mul : worth m u (p*q)≤worth m u p*worth m u q := by
  rw [MvPolynomial.mul_def]; simp_rw [MvPolynomial.sum_def]; apply (worth_sum m h u _ _).trans
  rw [worth,worth,Finset.sum_mul_sum]; apply sum_le_sum; intro i _; apply (worth_sum m h u _ _).trans; refine sum_le_sum fun j _ => ?_
  rw [worth_monomial,norm_mul]; exact (mul_le_mul_of_nonneg_right (fare_add m h u i j) (by positivity)).trans (le_of_eq (by ring))
lemma worth_prod (s:Finset Z) (f:Z→Packet I) : worth m u (∏ i∈s,f i)≤∏ i∈s,worth m u (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [prod_insert hi,prod_insert hi]; exact (worth_mul m h u _ _).trans (mul_le_mul_of_nonneg_left ih (worth_nonneg m h u _))
lemma worth_pow (n : ℕ) : worth m u (p^n) ≤ worth m u p ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,pow_succ]; exact (worth_mul m h u _ _).trans (mul_le_mul_of_nonneg_right ih (worth_nonneg m h u _))
omit h
end YM.FormalOPE.RG10.Route
