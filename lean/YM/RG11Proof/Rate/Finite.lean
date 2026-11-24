import YM.RG11Proof.Rate.Core
/-! Fixed-demand closure and finite-dimensional linear operations. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rate
open Filter
open scoped Topology BigOperators Classical

variable {α I J : Type*} {k : Budget α} (s : Finset I) {f g : I → α→ℝ} {p : I → ℝ}

theorem sum_bounded (H : ∀ i∈s, Bounded k (f i)) : Bounded k (fun a=>∑ i∈s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact (H i (by simp)).add (ih fun j hj=> H _ (by simp [hj]))
theorem prod_bounded (H : ∀ i∈s, Bounded k (f i)) : Bounded k (fun a=>∏ i∈s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact (H i (by simp)).mul (ih fun j hj=> H _ (by simp [hj]))

theorem sum_near (H : ∀ i∈s, Near k (f i) (p i)) : Near k (fun a=>∑ i∈s, f i a) (∑ i∈s,p i) := by
  classical
  induction s using Finset.induction_on with
  | empty=> simp
  | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (H _ (by simp)).add (ih fun j hj=> H _ (by simp [hj]))

theorem prod_near (H : ∀ i∈s, Near k (f i) (p i)) : Near k (fun a=>∏ i∈s, f i a) (∏ i∈s,p i) := by
  classical
  induction s using Finset.induction_on with
  | empty=> simp
  | insert i s hi ih=>simp_rw [Finset.prod_insert hi]; exact (H _ (by simp)).mul (ih fun j hj=>H _ (by simp [hj]))

theorem sum_nearFn (H : ∀ i∈s,NearFn k (f i) (g i)) : NearFn k (fun a=>∑ i∈s,f i a) (fun a=> ∑ i∈s,g i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.sum_empty]; exact NearFn.refl _
  | insert i s hi ih => simp_rw [Finset.sum_insert hi]; exact (H _ (by simp)).add (ih fun j hj=> H _ (by simp [hj]))

theorem prod_nearFn (H : ∀ i∈s,NearFn k (f i) (g i)) (hf : ∀ i∈s,Bounded k (f i)) :
    NearFn k (fun a=>∏ i∈s,f i a) (fun a=> ∏ i∈s,g i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.prod_empty]; exact NearFn.refl _
  | insert i s he ih =>
    have Hs : ∀ j∈s,NearFn k (f j) (g j):=fun j hj=> H _ (by simp [hj])
    have hfs : ∀ j∈s,Bounded k (f j):=fun j hj=> hf _ (by simp [hj])
    simp_rw [Finset.prod_insert he]
    exact (H _ (by simp)).mul (ih Hs hfs) (hf _ (by simp)) (prod_bounded _ (fun j hj=> (Hs j hj).symm.compare_bound (hfs j hj)))

variable [Fintype I] [DecidableEq I] (L : (I→ℝ)→ₗ[ℝ] ℝ)
theorem linear_eq (p : I→ℝ) : L p=∑ i,p i* L (fun j=> if j=i then 1 else 0) := by
  classical
  let M (i : I) : I→ℝ := fun j=> if j=i then 1 else 0
  have he : p=∑ i,p i • M i := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j) ?_]
    · simp [M]
    intro i _ hi; simp [M,Ne.symm hi]
  trans L (∑ i,p i • M i); · rw [← he]
  rw [map_sum]; simp_rw [map_smul,smul_eq_mul]; congr!

theorem linear_bounded (H : ∀ i, Bounded k (f i)) : Bounded k (fun a=> L (fun i=> f i a)) := by
  rw [show (fun a=>L (fun i=>f i a))=_ from funext fun a=>linear_eq (I:=I) L (fun i=>f i a)]
  exact sum_bounded Finset.univ (fun i _=> (H i).mul (Bounded.const _))

theorem linear_near (H : ∀ i, Near k (f i) (p i)) : Near k (fun a=> L (fun i=> f i a)) (L p) := by
  rw [show (fun a=>L (fun i=>f i a))=_ from funext fun a=>linear_eq (I:=I) L (fun i=>f i a), linear_eq L p]
  exact sum_near Finset.univ (fun i _=> (H i).mul (Near.const _))
end YM.RG11.Rate
