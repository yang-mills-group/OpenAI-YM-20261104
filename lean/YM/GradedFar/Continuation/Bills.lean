import YM.GradedFar.FormalSecond
import YM.GradedFar.Continuation.Windows

/-! Carry the same prices through evaluation on moving geometry. -/
namespace YM.FVA2.GradedFar.Continuation
noncomputable section
open Filter Set Real Topology Function
open O.Enh
open scoped Topology BigOperators Classical

-- convenient general pricing system for the first line of M.2:
-- thermal and log charts in same filter; post carries every T-power.
structure Board (I : Type) where
  l : Filter I
  s : I → ℝ
  g : I → ℝ
  spacious : Tendsto s l atTop
  shrinking : Tendsto g l (𝓝 0)
  positive : ∀ᶠ i in l, 0 < g i

def boarded {G : Gauge} (simple : G.Simple) (Q : Set Window) : Board Window where
  l := Window.windows Q
  s := Window.sep
  g := gYM G ∘ Window.len
  spacious := Window.windows_separation Q
  shrinking := (shrink simple).comp (Window.windows_short Q)
  positive := (Window.windows_short Q).eventually (positive_g simple)

def pack {I J : Type} (b : Board I) (f : J → I) : Board J where
  l := comap f b.l
  s := b.s ∘ f
  g := b.g ∘ f
  spacious := b.spacious.comp tendsto_comap
  shrinking := b.shrinking.comp tendsto_comap
  positive := tendsto_comap.eventually b.positive
section
variable {I J E : Type} {b : Board I} {v w a : ℝ} {f t : I → ℝ}
variable [NormedAddCommGroup E]

def Bill (b : Board I) (p : ℕ) (v : ℝ) (F : I → E) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ i in b.l, ‖F i‖ ≤ C*b.g i^p * post v (b.s i) a

namespace Bill
variable {F Q R : I → E} {p q : ℕ}
lemma of_rain {F : J → ℝ → E} (h : Rain v F) (r : I → J) : Bill b 0 v (fun i => F (r i) (b.s i)) := by
  obtain ⟨C,hC,k,h⟩ := h
  refine ⟨C,hC,k,?_⟩
  filter_upwards [b.spacious.eventually h] with i hi; rw [pow_zero,mul_one]; exact hi _
lemma of_bounded (b : Board I) (C : ℝ) (h : ∀ᶠ i in b.l, ‖F i‖ ≤ C) : Bill b 0 0 F := by
  refine ⟨max C 1, lt_max_of_lt_right zero_lt_one,0,?_⟩
  filter_upwards [h] with i hi
  simpa only [post,neg_zero,zero_mul,exp_zero,pow_zero,mul_one] using hi.trans (le_max_left ..)
lemma mono_fee (h : Bill b p a F) (hv : v ≤ a) (hp : q ≤ p) : Bill b q v F := by
  obtain ⟨C,hC,k,h⟩ := h; refine ⟨C,hC,k,?_⟩
  filter_upwards [h,b.positive, b.spacious.eventually_ge_atTop 0, b.shrinking.eventually_lt_const zero_lt_one] with i hi hg ht hh
  apply hi.trans
  refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg.le hh.le hp) hC.le) ?_
    (post_at ht).le (by positivity)
  unfold post; gcongr
lemma of_le (h : Bill b p v F) (hf : ∀ᶠ i in b.l, ‖Q i‖ ≤ ‖F i‖) : Bill b p v Q := by
  obtain ⟨C,hC,k,h⟩ := h; exact ⟨C,hC,k,hf.mp (by filter_upwards [h] with i hi hv using hv.trans hi)⟩
lemma pull (h : Bill b p v F) (f : J → I) : Bill (pack b f) p v (F ∘ f) := by
  obtain ⟨C,hC,k,h⟩ := h; exact ⟨C,hC,k,tendsto_comap.eventually h⟩
lemma apply_eq (h : Bill b p v F) (he : ∀ᶠ i in b.l, F i=Q i) : Bill b p v Q :=
  h.of_le (by filter_upwards [he] with i hi using le_of_eq (congrArg _ hi.symm))
lemma from_zero (b : Board I) : Bill b p v (fun _ => (0:E)) := by
  refine ⟨1,zero_lt_one,0,?_⟩
  filter_upwards [b.positive, b.spacious.eventually_ge_atTop 0] with i hg hs
  unfold post; rw [norm_zero]; positivity
lemma neg (h : Bill b p v F) : Bill b p v (fun i => -F i) :=
  h.of_le (by filter_upwards with i; rw [norm_neg])
lemma plus (h : Bill b p v F) (hq : Bill b p v Q) : Bill b p v (fun i => F i+Q i) := by
  obtain ⟨C,hC,k,h⟩ := h; obtain ⟨D,hD,n,hq⟩ := hq
  refine ⟨C+D, add_pos hC hD, k+n,?_⟩
  filter_upwards [h,hq,b.positive, b.spacious.eventually_ge_atTop 0] with i hi hi' hg hs
  apply ((norm_add_le ..).trans (add_le_add hi hi')).trans
  rw [add_mul,add_mul]; unfold post; gcongr <;> (first | omega | linarith)
lemma minus (h : Bill b p v F) (hq : Bill b p v Q) : Bill b p v (fun i => F i-Q i) := by
  simpa only [sub_eq_add_neg] using h.plus hq.neg
lemma sum (s : Finset J) {F : J → I → E} (h : ∀ i ∈ s, Bill b p a (F i)) :
    Bill b p a (fun i => ∑ j ∈ s, F j i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact from_zero b
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact plus (h _ (Finset.mem_insert_self ..)) (ih fun j hj => h _ (Finset.mem_insert_of_mem hj))
variable {F Q : I → ℂ}
lemma prod (h : Bill b p v F) (he : Bill b q w Q) : Bill b (p+q) (v+w) (fun i => F i*Q i) := by
  obtain ⟨C,hC,k,h⟩ := h; obtain ⟨D,hD,l,he⟩ := he
  refine ⟨C*D,mul_pos hC hD,k+l,?_⟩
  filter_upwards [h,he,b.positive,b.spacious.eventually_ge_atTop 0] with i hi hi' hg hs
  rw [norm_mul]
  apply (mul_le_mul hi hi' (norm_nonneg _) ((norm_nonneg _).trans hi)).trans_eq
  rw [pow_add]; unfold post; rw [neg_add,add_mul,exp_add,pow_add]; ring
lemma times (h : Bill b 0 v F) (he : Bill b p w Q) : Bill b p (v+w) (fun i => F i*Q i) := by
  simpa only [zero_add] using prod h he
lemma earns (h : Bill b p v F) (he : Bill b 0 w Q) : Bill b p (v+w) (fun i => F i*Q i) := by
  simpa only [add_zero] using prod h he
lemma product (s : Finset J) (a : J → ℝ) {F : J → I → ℂ} (h : ∀ i ∈ s, Bill b 0 (a i) (F i)) :
    Bill b 0 (∑ j ∈ s, a j) (fun i => ∏ j ∈ s, F j i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.prod_empty] using
      of_bounded (F:=fun _ => (1:ℂ)) b 1 (by filter_upwards with i; rw [norm_one])
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi,Finset.prod_insert hi]
      exact times (h i (Finset.mem_insert_self ..)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
end Bill
end
end
end YM.FVA2.GradedFar.Continuation
