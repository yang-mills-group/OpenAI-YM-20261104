import YM.FormalOPE.RG10.Routes.Rank

/-!
# Channel moment norm (semi on rows through finite order)

Addresses, geometry and parent ownership must be supplied in using these on formal kernel
transactions and stable components. Algebra retains complex phases, not the actual texture.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open Function Finset Marker Extra.Trajectories PowerSeries MeasureTheory Filter
open scoped Topology BigOperators Classical
variable {I : Type} (w v : I→ℝ) (n r : ℕ) (h : 0≤w) (P Q : Channel I)
-- Convolution lemma
lemma triangle_le (C : ℕ × ℕ → ℝ) (H : ∀ i, 0 ≤ C i) :
    (∑ i∈ range (r+1),∑ z∈ antidiagonal i,C z) ≤ ∑ i∈range (r+1),∑ j∈range (r+1), C (i,j) := by
  let U:= range (r+1); let T:=U.biUnion (fun i=> antidiagonal i); rw [← sum_biUnion, ← sum_product' U U (fun i j=> C (i,j))];
  · apply sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => H i)
    intro x hx; rcases mem_biUnion.mp hx with ⟨i, hi,hh⟩; have ht:= Finset.mem_antidiagonal.mp hh; simp only [Finset.mem_range] at hi; simp [U]; omega
  intro i _ j _ he; apply Finset.disjoint_left.mpr; intro a ha hb; exact he ((Finset.mem_antidiagonal.mp ha).symm.trans (Finset.mem_antidiagonal.mp hb))

def mag (w : I→ℝ) (n r : ℕ) (P : Channel I) := ∑ i∈ range (r+1),worth w n (coeff i P)
include h
lemma mag_sign : 0 ≤ mag w n r P := sum_nonneg fun _ _ => worth_nonneg w h n _
lemma current (i) (hi : i≤r) : worth w n (coeff i P) ≤ mag w n r P := single_le_sum (fun k _=>worth_nonneg w h n (coeff k P)) (mem_range.mpr (by omega))
lemma times_le (t : ℕ) (ht : n≤t) : mag w n r P≤mag w t r P := sum_le_sum fun _ _ => worth_order w h n _ ht
lemma frames_le (t : ℕ) (ht : r≤t) : mag w n r P≤mag w n t P := sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun i _ _=>worth_nonneg w h n (coeff i P))
lemma w_le (hm : w ≤ v) : mag w n r P ≤ mag v n r P := sum_le_sum fun _ _ => worth_mono hm h n _
omit h
@[simp] lemma mag_empty : mag w n r 0=0 := by simp [mag]
lemma mag_neg : mag w n r (-P)=mag w n r P := by simp [mag,worth_neg]
lemma mag_ext (h : Through r P Q): mag w n r P=mag w n r Q:= sum_congr rfl fun i hi=> by rw [h i (by simp only [mem_range] at hi; omega)]
lemma mag_smul (x : ℂ) : mag w n r (x • P)= ‖x‖*mag w n r P := by simp_rw [mag, coeff_smul,worth_smul,Finset.mul_sum]
lemma mag_one : mag w n r 1 = 1 := by
  unfold mag; rw [sum_eq_single 0];
  · simp
  · intro i hi ht; simp [ht]
  simp
include h
lemma mag_add : mag w n r (P+Q)≤ mag w n r P+mag w n r Q := by
  unfold mag; rw [← Finset.sum_add_distrib]; refine sum_le_sum fun i _ => ?_; rw [map_add]; exact worth_add w h n _ _
lemma mag_sub : mag w n r (P-Q)≤ mag w n r P+mag w n r Q := by rw [sub_eq_add_neg, ← mag_neg w n r Q]; exact mag_add w n r h P _
lemma mag_sum {K : Type*} (T:Finset K) (Y: K→ Channel I) : mag w n r (∑ v∈T,Y v) ≤ ∑ v∈T,mag w n r (Y v) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert _ _ he ih => rw [sum_insert he,sum_insert he]; exact (mag_add w n r h _ _).trans (add_le_add_right ih _)
lemma mag_mul : mag w n r (P*Q) ≤ mag w n r P*mag w n r Q := by
  let U:= range (r+1); let A i:= worth w n (coeff i P); let B i:= worth w n (coeff i Q)
  let c (v : ℕ×ℕ) := A v.1 * B v.2
  apply le_trans (b:=∑ i∈U,∑ j∈antidiagonal i,c j) (sum_le_sum fun i _ => ?_) (le_trans (triangle_le r c ?_) ?_)
  · exact fun _ => mul_nonneg (worth_nonneg w h n _) (worth_nonneg w h n _)
  · unfold mag; rw [Finset.sum_mul_sum]
  rw [PowerSeries.coeff_mul]; apply (worth_sum w h n _ _).trans; exact sum_le_sum fun _ _ => worth_mul w h n _ _
lemma mag_prod {K : Type*} (T:Finset K) (Y : K→Channel I) : mag w n r (∏ v∈T,Y v) ≤ ∏ v∈T, mag w n r (Y v) := by
  induction T using Finset.induction_on with
  | empty => simp [mag_one]
  | insert _ _ he ih => rw [prod_insert he, prod_insert he]; exact (mag_mul w n r h _ _).trans (mul_le_mul_of_nonneg_left ih (mag_sign w n r h _))
lemma mag_pow (i : ℕ) : mag w n r (P^i) ≤ mag w n r P^i := by
  induction i with
  | zero => simp [mag_one]
  | succ k ih => rw [pow_succ,pow_succ]; exact (mag_mul w n r h _ _).trans (mul_le_mul_of_nonneg_right ih (mag_sign w n r h P))

variable {v}
include h
lemma ride {H:ℝ} (hh : 0 ≤ H) (hv : ∀ i, w i ≤ H+v i) (hi : 0 ≤ v) : mag w n r P ≤ tip H n *mag v n r P := by
  have ht i : along w i ≤ H+along v i := along_le _ _ (add_nonneg hh (along_nn hi i)) (fun j hj => (hv j).trans (by gcongr; exact le_along hj v))
  unfold mag; rw [Finset.mul_sum]; refine sum_le_sum fun i _ => ?_; unfold worth; rw [Finset.mul_sum]; apply sum_le_sum; intro a _
  rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ((tip_mono (ht _) (along_nn h _) n).trans (tip_add hh (along_nn hi _) n)) (norm_nonneg _)
end YM.FormalOPE.RG10.Route
