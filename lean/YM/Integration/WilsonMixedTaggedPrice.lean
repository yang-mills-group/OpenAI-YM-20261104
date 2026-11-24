import YM.RG05Readout.Many.Carry

/-!
The same coarse regular or forced activity can be projected twice from a
single original marker-algebra witness. The price of the difference is one
factor of the marked radius, independently of the number of allowed modes.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedPrice
open Finset Function Marker RG05Readout.Many MergeProof.Accent Lattice RG
open Push GridApprox.Nil AbsoluteSums
open scoped BigOperators Classical

variable {V W I Y : Type*} [DecidableEq V] [DecidableEq W]
variable {B : Census V} {C : Census W} {π : V → W}

def weight (tag : V → Bool) (z : ℂ) (v : V) : ℂ := if tag v then z else 1

omit [DecidableEq V] in
private theorem weight_le (tag : V → Bool) {z : ℂ} (hz : ‖z‖ ≤ 1) (v : V) :
    ‖weight tag z v‖ ≤ 1 := by
  unfold weight
  split
  · exact hz
  · simp

theorem product_difference (tag : V → Bool) {z : ℂ} (hz : ‖z‖ ≤ 1) (s : Finset V) :
    ‖(∏ i ∈ s, weight tag z i) - ∏ i ∈ s, weight tag 0 i‖ ≤ ‖z‖ := by
  by_cases ht : ∃ j ∈ s, tag j = true
  · obtain ⟨j,hj,ht⟩ := ht
    have hzero : (∏ i ∈ s, weight tag 0 i) = 0 :=
      Finset.prod_eq_zero hj (by simp [weight,ht])
    rw [hzero,sub_zero,← Finset.prod_erase_mul s _ hj,norm_mul]
    have he : ‖∏ i ∈ s.erase j, weight tag z i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => weight_le tag hz i)
    simpa only [weight,ht,↓reduceIte] using
      mul_le_of_le_one_left (norm_nonneg (weight tag z j)) he
  have he (j) (hj : j ∈ s) : tag j = false := by
    cases h : tag j
    · rfl
    · exact False.elim (ht ⟨j,hj,h⟩)
  have hs (k : ℂ) : (∏ i ∈ s, weight tag k i) = 1 :=
    Finset.prod_eq_one fun i hi => by simp [weight,he i hi]
  rw [hs,hs,sub_self,norm_zero]
  exact norm_nonneg _

variable {n : Side} {w : V → ℝ} {w' : W → ℝ} {S : I → Support n}
variable {F : I → Y → Poly B} {b : ℕ} {e c : ℝ}

private theorem difference_before (tag : V → Bool) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (h : Towed w S F b e c) :
    Towed w S (fun i U => YM.Multi.dilation B (weight tag z) (F i U) -
      YM.Multi.dilation B (weight tag 0) (F i U)) b e (‖z‖ * c) := by
  obtain ⟨a,sa,ha,head⟩ := h
  refine ⟨fun i=>‖z‖*a i,sa.mul_left _,fun x=>?_,fun i=>?_⟩
  · convert budget_scale (norm_nonneg z) (ha x) using 1
    ext j
    split_ifs <;> ring
  obtain ⟨u,hu,loc,price⟩ := head i
  refine ⟨fun x=>‖z‖*u x,fun x=>mul_nonneg (norm_nonneg _) (hu x),?_,?_⟩
  · intro U x
    change ‖(YM.Multi.dilation B (weight tag z) (F i U)).part x -
      (YM.Multi.dilation B (weight tag 0) (F i U)).part x‖ ≤ _
    rw [YM.Multi.dilation_part,YM.Multi.dilation_part,← sub_mul,norm_mul]
    exact mul_le_mul (product_difference tag hz x.val) (loc U x)
      (norm_nonneg _) (norm_nonneg _)
  calc
    wordsPrice w (fun x=>‖z‖*u x) = ‖z‖*wordsPrice w u := by
      unfold wordsPrice
      rw [mul_sum]
      exact sum_congr rfl fun _ _=>by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left price (norm_nonneg _)

private theorem ones (x : Poly B) : YM.Multi.dilation B (fun _=>1) x = x := by
  ext i
  simp [YM.Multi.dilation_part]

/-- One fine witness gives two genuine specializations and one uniform
root-summed difference budget. The proof also allows coincident root names. -/
theorem towed (hL : License C B π) (tag : V → Bool) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (h : Towed w S F b e c) (hp : ∀ v, w' (π v) ≤ w v)
    (hw : ∀ v, 0 < w v) (hW : ∀ v, 0 < w' v) :
    Towed w' S (fun i U=>feed (weight tag z) hL (F i U) -
      feed (weight tag 0) hL (F i U)) b e (‖z‖ * c) := by
  have ht := carry hL (fun _=>1) (difference_before tag hz h)
    (fun v=>by simpa using hp v) hw hW
  simpa only [feed,AlgHom.comp_apply,ones,map_sub] using ht

end YM.Integration.WilsonMixedTaggedPrice
