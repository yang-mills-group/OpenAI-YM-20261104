import YM.FormalOPE.RG10.Routes.Vantage

/-!
# Geometry of a one-step Join

Estimate for two held groups, roots attached. Fields of each group can evaluate anywhere
according to the decay in its own Lens. Prove suppression between profile sets in space, paid
across parent tree edges using charged fluctuation support of both fields. The other vertices
pin relatively; use true diameter only on those vacuum vertices. Output Lens charges any surviving
port (fine/coarse, including internal ports that didn't actually reach output). Weight includes
need to test about centers or unions of profile regions, with triangle costs explicit; if the
output Lens is another (e.g. centered only on A but joining a big remote profile of B), translate
to that norm before further estimation and pay the coarser geometry accordingly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open MvPolynomial Finset Marker Joins Joins.Gauss Function
open Primitives.GCC Grove Charge
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {X I J B V : Type} [Fintype J] [DecidableEq V]
variable {T : Tape X} (p : (I⊕B) → X) (A E O : Lens T)
variable (m : Index I B)

def diam (T : Tape X) := along (fun k : (I⊕B) × (I⊕B) => T.Δ (p k.1) (p k.2)) (m.support ×ˢ m.support)
lemma diam_nn : 0 ≤ diam p m T := along_nn (fun _ => T.sign ..) _
lemma diam_ge {a b} (h : a∈ m.support) (h' : b∈m.support) : T.Δ (p a) (p b) ≤ diam p m T := le_along (i:=(a,b)) (mem_product.mpr ⟨h,h'⟩) (fun k => T.Δ (p k.1) (p k.2))

def rangeOf := along (A.m ∘ p) m.support
lemma rangeOf_nn : 0 ≤ rangeOf p A m := along_nn (fun _ => A.sign _) _
lemma rangeOf_ge {a} (h : a∈m.support) : A.m (p a) ≤ rangeOf p A m := le_along h (A.m ∘ p)
lemma rangeOf_mono (h : O.m ≤ A.m) : rangeOf p O m ≤ rangeOf p A m := mono_along (le_refl m.support) _ _ (fun i _ => h (p i)) (fun i => A.sign (p i))

namespace Beams
local notation "d" => T.Δ
local notation "u" => (p ∘ Sum.inl)
private def radiance (T : Tape X) (z : I × I) := T.Δ ((p ∘ Sum.inl) z.1) ((p ∘ Sum.inl) z.2)

def crossedAt (T : Tape X) (i j : Index I B) := let A:= pipes i ×ˢ pipes j; if h:A.Nonempty then A.inf' h (fun z => radiance p T z) else 0
lemma attainable {i j : Index I B} (h : (pipes i ×ˢ pipes j).Nonempty) :
    ∃ a∈pipes i, ∃ b∈pipes j, d (u a) (u b) = crossedAt p T i j := by
  obtain ⟨z,hz,he⟩ := exists_mem_eq_inf' h (radiance p T)
  unfold crossedAt; dsimp only; rw [dif_pos h]; exact ⟨_,(mem_product.mp hz).1, _, (mem_product.mp hz).2, he.symm⟩
lemma crossedAt_le {i j : Index I B} {a b} (h : a∈pipes i) (h' : b∈pipes j) : crossedAt p T i j ≤ d (u a) (u b) := by
  have he : (a,b)∈pipes i ×ˢ pipes j := mem_product.mpr ⟨h,h'⟩
  unfold crossedAt; dsimp only; rw [dif_pos ⟨(a,b),he⟩]; exact inf'_le _ he
lemma crossedAt_nn (i j : Index I B) : 0 ≤ crossedAt p T i j := by
  unfold crossedAt; dsimp only; split; exacts [le_inf' _ _ (fun _ _ => T.sign ..), le_rfl]

variable (M : V→ Index I B)
variable {S : Finset V} {o b : V} (L : ℝ) {f : Parent V}
variable (hL : A.Spaced E L) (ha : O.m ≤ A.m) (he : O.m ≤ E.m) (hf : Good S {o} f) (ho : o∈S)
    (hb : b∈S)

def travels (T : Tape X) (f : Parent V) (i : V) := crossedAt p T (M (f i)) (M i)
def includes (f : Parent V) (S : Finset V) (R : Finset V) := ∀ i∈ S\R,(pipes (M (f i)) ×ˢ pipes (M i)).Nonempty
variable (hm : Beams.includes M f S {o})

def radius (o b i : V) (m : Index I B) := if i=o then rangeOf p A m else if i=b then rangeOf p E m else diam p m T
lemma radius_nn (i : V) : 0 ≤ radius p A E o b i (M i) := by unfold radius; split; exact rangeOf_nn ..; split <;> first | exact rangeOf_nn .. | exact diam_nn ..

local notation "l" => travels p M T f
local notation "w" => fun i => radius p A E o b i (M i)

def evaluated (Z : Finset V) (C : ℝ) (b : V) :=
    (∀ i∈Z,rangeOf p O (M i) ≤ C) ∧
    (b∈Z → L ≤ C) ∧
    (b∉Z → ∀ i∈Z,rangeOf p A (M i) ≤ C)
include ha
private lemma start (v : b≠o) : evaluated p A O M L {o} (w o) b := by
  simp only [radius,evaluated,if_true,mem_singleton,v,not_false_eq_true,false_implies,true_implies];
  exact ⟨fun i h => h.symm ▸ rangeOf_mono p A O (M o) ha, trivial, fun i h => h.symm ▸ le_rfl⟩ -- inspect

include hm
omit ha in
private lemma link (O : Lens T) (i : V) (hi : i∈S\{o}) : rangeOf p O (M i) ≤ rangeOf p O (M (f i))+l i+diam p (M i) T := by
  obtain ⟨a,ha,b,hb,h⟩ := attainable (T:=T) p (hm i hi)
  have ha':= rangeOf_ge p O (M (f i)) ((fine_mem ..).1 ha)
  have h' : l i=T.Δ (u a) (u b):=h.symm; rw [h']
  apply along_le _ _ (add_nonneg (add_nonneg (rangeOf_nn ..) (T.sign ..)) (diam_nn ..))
  intro k hk; have hh:= diam_ge (T:=T) p (M i) ((fine_mem ..).1 hb) hk
  change O.m (p k) ≤ _; change O.m (u a) ≤ _ at ha'; change T.Δ (u b) (p k) ≤ _ at hh
  linarith [O.path (u b) (u a),O.path (p k) (u b)]

include hL he
omit ha -- ha omit in some
private lemma bud {Z : Finset V} (h' : o∈Z) (i : V) (hi : i∈S \ Z) {C : ℝ} (hc : 0≤C)
    (hj : f i∈Z) (h : evaluated p A O M L Z C b) : evaluated p A O M L (insert i Z) (C + (l i + w i)) b := by
  obtain ⟨h1,h2,h3⟩:=h
  have hi1 := (mem_sdiff.mp hi).2
  have hi2 : i ≠ o := fun h => hi1 (h.symm ▸ h')
  have hi3 := (mem_sdiff.mp hi).1
  have hi4 : i∈S\{o}:=mem_sdiff.mpr ⟨hi3,fun h => hi2 (mem_singleton.mp h)⟩
  have hl : 0 ≤ l i:=crossedAt_nn ..; have hw := radius_nn p A E M (o:=o) (b:=b) i
  have hr : C ≤ C+(l i+w i) := le_add_of_nonneg_right (add_nonneg hl hw)
  by_cases hk : i=b
  · subst i
    refine ⟨fun k hk => ?_,fun _ => ?_,fun H=>False.elim (H (mem_insert_self ..))⟩
    · rcases mem_insert.mp hk with h|h
      · subst k; have h : rangeOf p O (M b) ≤ w b := by dsimp only [radius]; rw [if_neg hi2, if_pos rfl]; exact rangeOf_mono p E O (M b) he
        linarith
      exact (h1 k h).trans hr
    obtain ⟨a,ha,x,hx,h⟩ := attainable (T:=T) p (hm b hi4)
    have ha' : A.m (u a) ≤ C := (rangeOf_ge p A (M (f b)) ((fine_mem ..).1 ha)).trans (h3 hi1 _ hj)
    have he' : E.m (u x) ≤ w b := by dsimp only [radius]; rw [if_neg hi2,if_pos rfl]; exact rangeOf_ge p E (M b) ((fine_mem ..).1 hx)
    have h' : T.Δ (u a) (u x) = l b := h
    linarith [hL (u a) (u x)]
  refine ⟨?_,fun h => (h2 ((mem_insert.mp h).resolve_left (Ne.symm hk))).trans hr,?_⟩
  · intro k h; rcases mem_insert.mp h with h|h
    · subst k; have := link p M hm O i hi4; dsimp only [radius]; rw [if_neg hi2,if_neg hk]; linarith [h1 _ hj]
    exact (h1 _ h).trans hr
  intro h k ht; specialize h3 (fun H=> h (mem_insert_of_mem H)); rcases mem_insert.mp ht with h|h
  · subst k; have := link p M hm A i hi4; dsimp only [radius]; rw [if_neg hi2,if_neg hk]; linarith [h3 _ hj]
  exact (h3 _ h).trans hr

include hf
private theorem inside (Z : Finset V) (hZ : Z⊆S) (h' : o∈Z) {C : ℝ} (hc : 0≤C) (h : evaluated p A O M L Z C b) :
    evaluated p A O M L S (C + ∑ i∈S\Z,(l i+w i)) b := by
  obtain hh|hh := (S\Z).eq_empty_or_nonempty
  · rw [hh,sum_empty, add_zero]; rw [Subset.antisymm (sdiff_eq_empty_iff_subset.mp hh) hZ]; exact h
  obtain ⟨i, hi,hj⟩:= hf.finite (S\Z) (sdiff_subset_sdiff (Subset.refl _) (singleton_subset_iff.mpr h')) hh
  have hj' : f i∈Z:= by
    apply not_not.mp; exact fun H=> hj (mem_sdiff.mpr ⟨hf.goes i (sdiff_subset_sdiff (Subset.refl _) (singleton_subset_iff.mpr h') hi),H⟩)
  have ht := bud p A E O M L hL he hm h' i hi hc hj' h
  have hx := inside (insert i Z) (insert_subset (mem_sdiff.mp hi).1 hZ) (mem_insert_of_mem h')
      (add_nonneg hc (add_nonneg (crossedAt_nn ..) (radius_nn ..))) ht
  rw [leaves] at hx
  rw [← add_sum_erase (S\Z) (fun i => (l i+w i)) hi,← add_assoc]; exact hx
termination_by (S \ Z).card
decreasing_by rw [leaves,card_erase_of_mem hi]; have := card_pos.mpr hh; omega


def totals (p : (I⊕B)→ X) {T : Tape X} (A E : Lens T) (M : V→ Index I B) (S : Finset V) (o b : V) (f : Parent V) :=
    (∑ i∈S,radius p A E o b i (M i)) + ∑ i∈S \ {o}, travels p M T f i

include ho hb ha
theorem traveled (h : b≠o) : L ≤ totals p A E M S o b f ∧
    ∀ i∈S, rangeOf p O (M i) ≤ totals p A E M S o b f := by
  have hh := inside p A E O M L hL he hf hm {o} (singleton_subset_iff.mpr ho) (mem_singleton_self _) (radius_nn ..) (start p A E O M L ha h)
  have he : totals p A E M S o b f=w o +∑ i∈S\{o},(l i+w i):=by
    unfold totals; rw [sum_add_distrib,sdiff_singleton_eq_erase, ← add_sum_erase S (w ·) ho]; ring  -- inspect
  rw [he]; exact ⟨hh.2.1 hb,hh.1⟩
end Beams
end YM.FormalOPE.RG10.Route
