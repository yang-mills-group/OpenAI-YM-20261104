import YM.FormalOPE.RG10.Powers

/-! Taylor modules: coefficient weights for mixing fields/profiles. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10
open MeasureTheory PowerSeries Finset
open scoped BigOperators Classical

variable {Θ E : Type*} [Fintype Θ] [MeasurableSpace E] {F : FlatFeed Θ E}
    {W : Vertices (Θ × E)} {I : Type*}

namespace FlatFeed
variable {a b : Θ×E→ℂ} {A B : Kernel (Θ×E)}

lemma Pays.zero : F.Pays 0 := by intro θ; simp
lemma Pays.smul (ha : F.Pays a) (c : ℂ) : F.Pays (c • a) := by
  intro θ; simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm (b:=c)]; apply (ha θ).const_mul
lemma Pays.const (c : ℂ) : F.Pays (fun _ => c) := fun θ => ((F.density_integrable θ).ofReal).mul_const _
lemma Pays.add (ha : F.Pays a) (hb : F.Pays b) : F.Pays (a+b) := by
  intro θ; simp only [Pi.add_apply, mul_add]; exact (ha θ).add (hb θ)
lemma Pays.sum (s : Finset I) (f : I→Θ×E→ℂ) (hf : ∀ i∈s,F.Pays (f i)) : F.Pays (∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact Pays.zero
  | insert i s hi ih => rw [sum_insert hi]; apply (hf i (mem_insert_self ..)).add (ih (fun i h => hf i (mem_insert_of_mem h)))

lemma mean_add (ha : F.Pays a) (hb : F.Pays b) : F.mean (a+b) = F.mean a + F.mean b := by
  unfold mean
  simp_rw [← sum_add_distrib]
  apply sum_congr rfl; intro i hi
  rw [← mul_add, ← add_div]; congr 2
  simp_rw [Pi.add_apply, mul_add]; exact integral_add (ha i) (hb i)
lemma mean_smul (F : FlatFeed Θ E) (c : ℂ) (a : Θ × E → ℂ) : F.mean (c • a) = c * F.mean a := by
  unfold mean; rw [Finset.mul_sum]
  apply sum_congr rfl; intro i hi
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm (b:=c)]
  rw [integral_const_mul]; ring

lemma mean_sum (s : Finset I) (f : I→Θ × E→ℂ) (h : ∀ i∈s,F.Pays (f i)) :
    F.mean (∑ i∈s,f i) = ∑ i∈s,F.mean (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty,sum_empty,mean_zero];
  | insert i s hi ih =>
    have e := fun j hj => h j (mem_insert_of_mem hj)
    rw [sum_insert hi, sum_insert hi, mean_add (h i (mem_insert_self ..)) (Pays.sum s f e), ih e]

lemma Funded.zero : F.Funded 0 := by
  intro i; simpa only [row,Pi.zero_apply,map_zero] using! (Pays.zero (F:=F))
lemma Funded.add (hA : F.Funded A) (hB : F.Funded B) : F.Funded (A+B) := by
  intro i; have h := (hA i).add (hB i)
  simpa only [row, Pi.add_apply, map_add] using! h

lemma average_add (hA : F.Funded A) (hB : F.Funded B) : F.average (A+B) = F.average A + F.average B := by
  ext k : 1; rw [average_coeff,map_add,average_coeff,average_coeff, ← mean_add (hA k) (hB k)];
  apply congr_arg; funext x; simp [row]

lemma Funded.sum (s : Finset I) (f : I → Kernel (Θ × E)) (h : ∀ i∈s,F.Funded (f i)) :
    F.Funded (∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [sum_empty]; exact Funded.zero
  | insert i s hi ih => rw [sum_insert hi]; exact (h i (mem_insert_self ..)).add (ih fun j hj => h j (mem_insert_of_mem hj))

lemma average_sum (s : Finset I) (f : I → Kernel (Θ × E)) (h : ∀ i∈s,F.Funded (f i)) :
    F.average (∑ i∈s,f i) = ∑ i∈s,F.average (f i) := by
  apply PowerSeries.ext; intro i
  rw [average_coeff,map_sum]; simp_rw [average_coeff]
  rw [← mean_sum s (fun j => row i (f j)) (fun j hj => h j hj i)]
  congr!; funext; simp [row, Finset.sum_apply]
end FlatFeed

variable {X : Type*}
/-- Taylor-series mixing weights not necessarily at a common field grade yet. This is an honest
series *computed in the same coupling indeterminate.* -/
def outside {X : Type*} (c : Series) : Kernel X := fun _ => c

lemma row_external (c : Series) (f : Kernel X) (k : ℕ) : row k (outside c * f) =
    ∑ p∈antidiagonal k, coeff p.1 c • row p.2 f := by
  funext; simp [row, outside, Finset.sum_apply, coeff_mul]

namespace FlatFeed
variable {a : Kernel (Θ × E)}

lemma Funded.external (h : F.Funded a) (c : Series) : F.Funded (outside c * a) := by
  intro i; rw [row_external]; apply Pays.sum; exact fun p _ => (h p.2).smul _
lemma average_external (h : F.Funded a) (c : Series) : F.average (outside c * a) = c * F.average a := by
  apply PowerSeries.ext; intro k
  rw [coeff_mul, average_coeff, row_external, mean_sum]; simp_rw [mean_smul, average_coeff]
  exact fun p _ => (h p.2).smul _

lemma step_external (h : F.Funded (W.weight * a)) (c : Series) :
    F.step W (outside c * a) = c * F.step W a := by
  rw [step, mul_left_comm, average_external h, step, mul_assoc]

lemma step_sum (s : Finset I) (f : I → Kernel (Θ × E)) (h : ∀ i∈s,F.Funded (W.weight * f i)) :
    F.step W (∑ i∈s, f i) = ∑ i∈s, F.step W (f i) := by
  simp only [step]; rw [Finset.mul_sum, average_sum, Finset.sum_mul]; exact h

section Combinations
variable [Fintype I] {J : I → Type*} [∀ i, Fintype (J i)]
    (c : ∀ i, J i → Series) (f : ∀ i, J i → Kernel X)

/-- Complete choices across columns, no hidden multiplicity. -/
def combined (v : I) := ∑ i : J v, outside (c v i) * f v i

lemma combine_prod :
    ∏ i : I, combined c f i = ∑ j : ∀ i, J i, outside (∏ i : I,c i (j i)) * ∏ i, f i (j i) := by
  classical
  unfold combined; rw [Fintype.prod_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib]; congr! 1
  funext x; rw [Finset.prod_apply]; rfl
end Combinations
section
variable [Fintype I] {J : I → Type*} [∀ i, Fintype (J i)]
    (c : ∀ i, J i → Series) (f : ∀ i, J i → Kernel (Θ × E))
    (h : ∀ j : ∀ i, J i, F.Funded (W.weight * ∏ i, f i (j i)))

include h
omit [∀ i, Fintype (J i)] in
lemma charge_selection (j : ∀ i, J i) :
    F.Funded (W.weight * (outside (∏ i : I,c i (j i)) * ∏ i, f i (j i))) := by rw [mul_left_comm]; exact (h j).external _

theorem combination :
    F.Funded (W.weight * ∏ i, combined c f i) ∧
    F.ordinary W Finset.univ (combined c f) = ∑ j : ∀ i, J i, (∏ i : I,c i (j i)) * F.ordinary W Finset.univ (fun i => f i (j i)) := by
  classical
  constructor
  · rw [combine_prod, Finset.mul_sum]
    apply Funded.sum; exact fun j _ => charge_selection c f h j
  unfold ordinary; rw [combine_prod, step_sum];
  · exact sum_congr rfl fun j _ => step_external (h j) _
  exact fun j _ => charge_selection c f h j
end
end FlatFeed
end YM.FormalOPE.RG10
