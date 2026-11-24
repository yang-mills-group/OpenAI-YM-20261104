import YM.FormalOPE.RG10.Routes.Beams

/-!
# Output-root multiplier at any resolution

For each choice before summing, include the *two* needed power loads (output root and suppression),
even when the bound is then going to be used in a recurrence. Refinements can substitute
heterogeneous powers. Two vertices with Lens charges, all remaining are unmarked here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route.Beams
open MvPolynomial Finset Marker Joins Joins.Gauss Function
open Primitives.GCC Grove Charge
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {X I J B V : Type} [Fintype J] [DecidableEq V]
variable {T : Tape X} (p : (I⊕B) → X) (q : I → Row J)
variable (M : V→ Index I B)
local notation "d" => T.Δ
local notation "u" => (p ∘ Sum.inl)
variable {S : Finset V} {o b : V} {f : Parent V}
local notation "l" => travels p M T f

def coinAt (T : Tape X) (n : ℕ) (a b : I) := tip (T.Δ ((p ∘ Sum.inl) a) ((p ∘ Sum.inl) b)) n * crossing q a b
def credits (T : Tape X) (n : ℕ) (a b : Index I B) := ∑ i∈pipes a,∑ j∈pipes b,coinAt p q T n i j
lemma coinAt_nn (n : ℕ) (a b : I) : 0 ≤ coinAt p q T n a b := mul_nonneg (tip_pos (T.sign ..) _).le (crossing_nn ..)
lemma credits_nn (n : ℕ) (a b : Index I B) : 0 ≤ credits p q T n a b := sum_nonneg fun _ _ => sum_nonneg fun _ _ => coinAt_nn ..
local notation "c" => contact (fun (_:V) => q) (pipes ∘ M)
omit [DecidableEq V] in
lemma lifted (n : ℕ) (i j : V) : tip (crossedAt p T (M i) (M j)) n * (c i j) ≤ credits p q T n (M i) (M j) := by
  simp only [contact,credits,Function.comp_apply,Finset.mul_sum]
  apply sum_le_sum; intro a ha; refine sum_le_sum fun b hb => ?_; apply mul_le_mul_of_nonneg_right (tip_mono (crossedAt_le p ha hb) (crossedAt_nn ..) n) (abs_nonneg _)
lemma usable (H : beams S {o} f c ≠ 0) : includes M f S {o} := by
  intro i hi; apply not_not.mp; intro he; apply H; unfold beams; apply prod_eq_zero hi;
  rw [nonempty_product] at he;  -- inspect
  by_cases h : (pipes (M i)).Nonempty
  · have ha : ¬(pipes (M (f i))).Nonempty:= fun H=> he ⟨H,h⟩
    simp [contact,not_nonempty_iff_eq_empty.mp ha]
  simp [contact,not_nonempty_iff_eq_empty.mp h]
private lemma bundleTip {m : V → ℝ} (H : ∀ i∈S,0 ≤ m i) (n) : tip (∑ i∈S,m i) n ≤ ∏ i∈S, tip (m i) n := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hx:= H i (mem_insert_self ..); have ht (j:V) (hj:j∈S):= H _ (mem_insert_of_mem hj);
    rw [sum_insert hi,prod_insert hi]; exact (tip_add hx (sum_nonneg ht) n).trans (mul_le_mul_of_nonneg_left (ih ht) (tip_pos hx n).le)

variable (A E O : Lens T)
local notation "w" => fun i => radius p A E o b i (M i)
local notation "Z" => totals p A E M S o b f

lemma total_nn : 0 ≤ Z := add_nonneg (sum_nonneg (fun _ _ => radius_nn ..)) (sum_nonneg fun _ _ => crossedAt_nn ..)
lemma bundle (n) : tip Z n ≤ (∏ i∈S,tip (w i) n)*∏ i∈ S\{o},tip (l i) n := (tip_add
      (sum_nonneg (fun _ _ => radius_nn ..)) (sum_nonneg (fun _ _ => crossedAt_nn ..)) n).trans
    (mul_le_mul (bundleTip (fun _ _ => radius_nn ..) n) (bundleTip (fun _ _ => crossedAt_nn ..) n)
      (tip_pos (sum_nonneg fun _ _ => crossedAt_nn ..) n).le (prod_nonneg fun _ _ => (tip_pos (radius_nn ..) n).le))

lemma all_le {r : ℝ} (hr : 0 ≤ r) (h : ∀ i∈S,rangeOf p O (M i) ≤ r) :
    along (O.m ∘ p ∘ Sum.inr) (∑ i∈S,coarse (M i)).support ≤ r := by
  induction S using Finset.induction_on with
  | empty => simpa using hr
  | @insert i S hi ih =>
    have hx := h i (mem_insert_self ..);
    rw [sum_insert hi]; apply le_trans (along_add (O.m ∘ p ∘ Sum.inr) (fun t => O.sign (p (.inr t))) _ _) (max_le ?_ (ih (fun j hj=>h j (mem_insert_of_mem hj))))
    exact along_le _ _ hr fun a ha => (rangeOf_ge p O _ ((coarse_mem ..).1 ha)).trans hx
variable (n : ℕ) {L : ℝ} (hp : 0 ≤ L) (hL : A.Spaced E L) (ha : O.m ≤ A.m) (he : O.m ≤ E.m)
    (hf : Good S {o} f) (ho : o∈S) (hb : b∈S) (hne : b≠o)


include hp hL ha he hf ho hb hne in
/-- Polynomial rooted moment PLUS separation gain. In units of the operation. -/
theorem tipped : (fare (O.m ∘ p ∘ Sum.inr) n (∑ i : ↥S, coarse (M i.val))) * tip L n * beams S {o} f c ≤
    (∏ i∈S,tip (w i) (n+n))*beams S {o} f (fun i j => credits p q T (n+n) (M i) (M j)) := by
  by_cases h : beams S {o} f c=0
  · rw [h,mul_zero]; exact mul_nonneg (prod_nonneg fun _ _ => (tip_pos (radius_nn ..) _).le) (prod_nonneg fun _ _ => credits_nn ..)
  obtain ⟨hx,ht⟩:= traveled p A E O M L hL ha he hf ho hb (usable q M h) hne -- inspect
  have hr : (fare (O.m ∘ p ∘ Sum.inr) n (∑ i : ↥S, coarse (M i.val))) ≤ tip Z n := by
    unfold fare; rw [Finset.sum_coe_sort S (fun i => coarse (M i))]; exact tip_mono (all_le p M O (total_nn ..) ht) (along_nn (fun i => O.sign (p (.inr i))) _) _
  have hh : (fare (O.m ∘ p ∘ Sum.inr) n (∑ i : ↥S, coarse (M i.val)))*tip L n ≤ tip Z (n+n) := by rw [tip,tip,pow_add]; exact mul_le_mul hr (tip_mono hx hp n) (tip_pos hp n).le (tip_pos (total_nn ..) _).le
  apply (mul_le_mul_of_nonneg_right (hh.trans (bundle ..)) (prod_nonneg fun _ _ => contact_nn ..)).trans
  rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun _ _ => (tip_pos (radius_nn ..) _).le)
  unfold beams; rw [← prod_mul_distrib]; exact prod_le_prod (fun _ _ => mul_nonneg (tip_pos (crossedAt_nn ..) _).le (contact_nn ..)) (fun _ _ => lifted ..)
end YM.FormalOPE.RG10.Route.Beams
