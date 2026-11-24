import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Forests
import YM.FormalOPE.RG10.Routes.Legs

/-!
# Count only the displayed rooted kernel budgets

Independent finite-arity lemma: can read different root assignments with no factorial or volume
price other than those asked for each held (gaussian) port. Adapt `Good` from accepted GCC
(canonical forest edges). Recurses from the root out along buds, so no leaf rebranch argument or
uncontrolled multiplicities on the unfilled locus. All assignment hypotheses apply regardless of
parent selection only at actually admitted indices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route.Count
open MvPolynomial Finset Marker Function Fintype
open Primitives.GCC Grove
open scoped Topology BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] {K : Type*} [Zero K] [DecidableEq K]
variable (S : Finset V) {o : V} (W : V→ Finset K) (u : V → K → ℝ) (w : V → K → K → ℝ)
local notation "Σπ" => Fintype.piFinset

/-- Restrict to current tree, fixing the remaining choices. -/
def fill (Z : Finset V) (P : V→K) (v) := if v∈S\Z then W v else {P v}
omit [Fintype V] [Zero K] [DecidableEq K] in
lemma fill_update {Z : Finset V} {j : V} (_h : j∈S\Z) (P : V→ K) (k:K) :
    fill S W (insert j Z) (Function.update P j k)= Function.update (fill S W Z P) j {k} := by
  ext i; unfold fill; simp only [leaves]; by_cases hi : i=j
  · subst i; simp
  rw [update_of_ne hi,update_of_ne hi]; simp [hi]

omit [Zero K] in
lemma divide {Z : Finset V} {j : V} (h : j∈S\Z) (P : V→ K) (g : (V→K)→ℝ) :
    (∑ M∈Σπ (fill S W Z P),g M)=∑ i∈W j,∑ M∈Σπ (fill S W (insert j Z) (update P j i)),g M := by
  let U:=Σπ (fill S W Z P)
  suffices (∑ M∈U,g M)=∑ i∈W j,∑ M∈U.filter (fun M => M j=i),g M by
    refine this.trans (sum_congr rfl (fun i hi => ?_)); rw [fill_update S W h,piFinset_update_singleton_eq_filter_piFinset_eq]
    exact (show i∈fill S W Z P j from by rwa [fill,if_pos h])
  symm
  apply Finset.sum_fiberwise_of_maps_to (g:=fun M : V→ K => M j); intro M hm; simpa only [fill,if_pos h] using mem_piFinset.mp hm j

variable (C : V→ℝ) (f : Parent V)

private def growing (Z : Finset V) (M : V→K) := ∏ i∈ S\Z,u i (M i)*w i (M (f i)) (M i)

-- u node, w incident
variable (hu : ∀ i∈S, ∀ a∈W i,0 ≤ u i a)
    (hw : ∀ i∈ S\{o},∀ a∈W (f i),∀ b∈W i,0 ≤ w i a b)
    (hv : ∀ i∈ S\{o},∀ a∈W (f i),∑ b∈W i,u i b*w i a b ≤ C i)
    (hc : ∀ i∈S, 0 ≤ C i) (hf : Good S {o} f)
local notation "Y" => growing S u w f
include hu hw hv hc hf in
omit [Zero K] in
private theorem apart (Z : Finset V) (hz : Z⊆S) (hp : o∈Z) (M₀ : V→K) (hM : ∀ i∈Z, M₀ i∈W i) :
    ∑ M∈Σπ (fill S W Z M₀), growing S u w f Z M≤∏ i∈S\Z,C i := by
  obtain he|he := (S\Z).eq_empty_or_nonempty
  · simp [fill,he,growing]
  have hsub : S\Z ⊆ S\{o} := sdiff_subset_sdiff (Subset.refl _) (singleton_subset_iff.mpr hp)
  obtain ⟨i,hi,hj⟩:= hf.finite (S\Z) hsub he
  obtain ⟨he₁,he₂⟩:=mem_sdiff.mp hi
  have hw' : f i∈Z:= not_not.mp (fun h => hj (mem_sdiff.mpr ⟨hf.goes i (hsub hi),h⟩))
  have hN : f i≠i := fun h=> he₂ (h ▸ hw')
  let c a := u i a*w i (M₀ (f i)) a
  let Z':=insert i Z; let Q := ∏ j∈S\Z', C j
  rw [divide S W hi];
  have hm (a : K) (ha : a∈W i):=(show ∀ k∈Z', update M₀ i a k∈W k from fun k hk=> by
    rcases mem_insert.mp hk with h|h
    · subst k; simpa
    rw [update_of_ne (show k≠i from fun he=>he₂ (he ▸ h))]; exact hM k h)
  refine le_trans (b:=∑ a∈W i,c a*Q) (sum_le_sum fun a ha => ?_) ?_
  · have hh M (hh : M∈Σπ (fill S W Z' (update M₀ i a))) (j : V) (hj : j∈Z') : M j=update M₀ i a j := by simpa only [fill,if_neg (show j∉S\Z' from fun h=>(mem_sdiff.mp h).2 hj),mem_singleton] using (mem_piFinset.mp hh j)
    have ht M (h : M∈Σπ (fill S W Z' (update M₀ i a))) : Y Z M = c a*Y Z' M := by
      rw [growing,← mul_prod_erase _ _ hi]
      conv_lhs => lhs; rw [hh M h (f i) (mem_insert_of_mem hw'),hh M h i (mem_insert_self ..),update_self,update_of_ne hN]
      unfold growing Z'; rw [leaves]
    have hn:= apart Z' (insert_subset he₁ hz) (mem_insert_of_mem hp) (update M₀ i a) (hm a ha)
    rw [sum_congr rfl ht,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hn (mul_nonneg (hu i he₁ a ha) (hw i (hsub hi) _ (hM _ hw') _ ha))
  rw [← Finset.sum_mul,← mul_prod_erase _ _ hi]; apply mul_le_mul ?_ (show Q ≤ _ from by unfold Q Z'; rw [leaves]) ?_ (hc i he₁)
  · exact hv i (hsub hi) _ (hM _ hw')
  exact prod_nonneg (fun j hj=>hc j (sdiff_subset hj))
termination_by (S \ Z).card
decreasing_by rw [leaves,card_erase_of_mem hi]; have := card_pos.mpr he; omega

def tour (o : V) (M : V→K) := u o (M o) * growing S u w f {o} M
omit [Zero K] [Fintype V] [DecidableEq K] in
lemma touring (o:V) (M : V→K) : tour S u w f o M= u o (M o) * ∏ i∈ S\{o}, u i (M i)*w i (M (f i)) (M i) := rfl
variable (ho:o∈S)
include hu hw hv hc hf ho in
theorem price : ∑ M∈Σπ (fill S W ∅ 0),tour S u w f o M ≤ (∑ a∈W o,u o a) * ∏ i∈S\{o}, C i := by
  rw [divide S W (j:=o) (by simp [ho]),Finset.sum_mul]; apply sum_le_sum; intro a ha
  have he : insert o ∅=({o} : Finset V):= rfl
  rw [he];
  let t:= update (fun _:V=> (0:K)) o a; let β:= Σπ (fill S W {o} t)
  have ht M (h : M∈β) : tour S u w f o M= u o a*Y {o} M := by
    have : M o=a:=by simpa [fill,t] using (mem_piFinset.mp h o )
    unfold tour; rw [this]
  change β.sum _ ≤ _
  rw [sum_congr rfl ht,← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left ?_ (hu _ ho _ ha)
  exact apart S W u w C f hu hw hv hc hf _ (by simpa) (mem_singleton_self o) t (by simpa [t])
end YM.FormalOPE.RG10.Route.Count
