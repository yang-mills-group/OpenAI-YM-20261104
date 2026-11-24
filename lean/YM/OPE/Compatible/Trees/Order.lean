import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Order.BoundedOrder.Basic

/-!
# Finite Euclidean cluster trees, cuts

Ancestor ≤, start with bottom (root). `Origin` states the tree law:
linear order on the predecessor path of each vertex. Includes unary vertices,
doesn't impose regular degrees, height, or edge spacing. This is just a
finite rooted tree convention (take the usual ancestor order on a rooted
tree). Parent-to-v edge is specified by `par`; it is the bottom edge if
there are no proper ancestors except the root. The root will itself need an
OPE, i.e. be an internal vertex with child slots. There is no nesting
operation rooted at a stand-alone leaf label (for the product of a single
label against exteriors at declared radius can always use one internal root
with one leaf).

`Crown` = downward-closed set of actual internal vertices still active. Its
direct children not in the set, `brim`, are the frontier leaf inputs. To
collapse at internal v delete v *and its whole active subtree* with trim,
so v becomes a leaf carrying, for example, an intermediate field. This
lets the rate estimates use different horizons at different stages internally;
definition of the true nesting will always use the requested ones.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace YM.OPE.Arboreal
variable {V : Type} [PartialOrder V] [OrderBot V]

structure Origin (V:Type) [PartialOrder V] : Prop where
  path {a b v : V} : a ≤ v → b ≤ v → a ≤ b ∨ b ≤ a
variable [Fintype V] (E : Origin V)

-- includes direct parents
include E in
lemma exists_par {v : V} (h : v ≠ ⊥) : ∃ u : V, u < v ∧ ∀ w : V, w < v → w ≤ u := by
  let S := Finset.univ.filter fun i:V => i < v
  have he (i:V) : i ∈ S ↔ i < v := by simp [S]
  obtain ⟨u,hU⟩ := S.exists_maximal (show S.Nonempty from ⟨⊥,(he ⊥).mpr (bot_lt_iff_ne_bot.mpr h)⟩)
  have hu := (he u).mp hU.1
  refine ⟨u,hu,fun w hw => ?_⟩
  exact (E.path hw.le hu.le).elim id (fun hh => hU.2 ((he w).mpr hw) hh)

def par (v : V) := if h:v=⊥ then ⊥ else Classical.choose (exists_par E h)
lemma from_par {v : V} (h : v ≠ ⊥) : par E v < v := by
  rw [par,dif_neg h]; exact (Classical.choose_spec (exists_par E h)).1
lemma touch_par {v w : V} (h : w < v) : w ≤ par E v := by
  have hw := bot_lt_iff_ne_bot.mp (lt_of_le_of_lt bot_le h)
  rw [par,dif_neg hw]; exact (Classical.choose_spec (exists_par E hw)).2 w h
lemma par_le (v : V) : par E v ≤ v := by
  by_cases he : v=⊥
  · simp [he,par]
  exact (from_par E he).le

include E in
lemma exists_couple (x y:V) : ∃ v:V, v ≤ x ∧ v ≤ y ∧ ∀ w:V, w ≤ x → w ≤ y → w ≤ v := by
  let S := Finset.univ.filter fun i:V => i ≤ x ∧ i ≤ y
  have he (i:V) : i∈S ↔ i ≤ x ∧ i ≤ y := by simp [S]
  obtain ⟨v,hv⟩ := S.exists_maximal (show S.Nonempty from ⟨⊥,(he ⊥).mpr ⟨bot_le,bot_le⟩⟩)
  obtain ⟨hx,hy⟩ := (he v).mp hv.1
  exact ⟨v,hx,hy,fun w hw ht => (E.path hw hx).elim id (fun h => hv.2 ((he w).mpr ⟨hw,ht⟩) h)⟩

def couple (x y : V) := (exists_couple E x y).choose
lemma coupled_left (x y : V) : couple E x y ≤ x := (exists_couple E x y).choose_spec.1
lemma coupled_right (x y : V) : couple E x y ≤ y := (exists_couple E x y).choose_spec.2.1
lemma ancestors_couple {x y v : V} (hx : v ≤ x) (hy : v ≤ y) : v ≤ couple E x y :=
  (exists_couple E x y).choose_spec.2.2 v hx hy
lemma separate_left {x y:V} (h : ¬ x ≤ y) : couple E x y < x :=
  lt_of_le_of_ne (coupled_left ..) (fun e => h (e ▸ coupled_right E x y))
lemma separate_right {x y:V} (h : ¬ y ≤ x) : couple E x y < y :=
  lt_of_le_of_ne (coupled_right ..) (fun e => h (e ▸ coupled_left E x y))

-- path induction used also for finding the child under a strict ancestor
lemma journey {P : V → Prop} (h : P ⊥) (w : ∀ i ≠ ⊥, P (par E i) → P i) (v : V) : P v := by
  apply (Finite.wellFounded_of_trans_of_irrefl (α:=V) LT.lt).induction v
  intro u ih
  by_cases hu : u = ⊥
  · rwa [hu]
  exact w _ hu (ih _ (from_par E hu))

include E in
lemma foot {x y:V} (h : x < y) : ∃ i:V, x < i ∧ par E i=x ∧ i ≤ y := by
  revert h
  apply journey E (P:=fun i:V => x < i → ∃ j:V, x < j ∧ par E j=x ∧ j ≤ i) (fun h => False.elim (not_lt_bot h))
  intro i hi ih ht
  rcases (touch_par E ht).lt_or_eq with h|h
  · obtain ⟨j,hj,e,h⟩ := ih h; exact ⟨j,hj,e,h.trans (par_le ..)⟩
  exact ⟨i,ht,h.symm,le_rfl⟩

def strictChildren (v : V) : Finset V := .filter (fun i : V => v < i ∧ par E i=v) Finset.univ
@[simp] lemma kid_mem {v i : V} : i∈ strictChildren E v ↔ v < i ∧ par E i=v := by simp [strictChildren]
def heart (V : Type) [PartialOrder V] [Fintype V] : Finset V :=
  Finset.univ.filter fun v => ∃ x, v < x
omit [OrderBot V] in
@[simp] lemma heart_mem {v : V} : v∈ heart V ↔ ∃ x, v < x := by simp [heart]
omit [OrderBot V] in
lemma internal_le {v w : V} (h : v∈ heart V) (hw : w ≤ v) : w∈ heart V :=
  (heart_mem).2 ((heart_mem.1 h).imp fun _ e => lt_of_le_of_lt hw e)
lemma kids_heart {v:V} : (strictChildren E v).Nonempty ↔ v∈heart V := by
  constructor
  · rintro ⟨i,hi⟩; exact heart_mem.mpr ⟨i,((kid_mem E).mp hi).1⟩
  intro h; obtain ⟨j,hj⟩ := heart_mem.mp h; obtain ⟨i,hi,hp,-⟩ := foot E hj
  exact ⟨i,(kid_mem E).mpr ⟨hi,hp⟩⟩

structure Crown (P : Finset V) : Prop where
  base : ⊥ ∈ P
  inner : P ⊆ heart V
  roots {u v} : u ≤ v → v∈P → u∈P
lemma tall {V:Type} [PartialOrder V] [OrderBot V] [Fintype V] (h : ⊥∈ heart V) : Crown (heart V) :=
  ⟨h,Finset.Subset.refl _,fun _ hv => internal_le hv (by assumption)⟩

variable (P:Finset V)
def brim := Finset.univ.filter (fun i:V => i∉P ∧ i≠⊥ ∧ par E i∈P)
@[simp] lemma on_brim {i:V} : i ∈ brim E P ↔ i∉P ∧ i≠⊥ ∧ par E i∈P := by simp [brim]
lemma brim_apart (hP : Crown P) {i j : V} (hi : i∈brim E P) (hj : j∈brim E P) (h : i≠j) : ¬ i ≤ j :=
  fun e => ((on_brim ..).mp hi).1 (hP.roots (touch_par E (lt_of_le_of_ne e h)) (((on_brim ..).mp hj).2.2))
lemma maximalLeaves (h : ⊥∈ heart V) {x : V} : x∈ brim E (heart V) ↔ ¬∃ y, x < y := by
  rw [on_brim]; simp only [heart_mem]; constructor
  · exact And.left
  intro he
  have hx : x ≠ ⊥ := fun e => he (heart_mem.mp (e.symm ▸ h))
  exact ⟨he,hx,x,from_par E hx⟩

def trim (v : V) := P.filter (fun i => ¬ v ≤ i)
omit [Fintype V] [OrderBot V] in
lemma lighter {v:V} (hv:v∈P) : trim P v ⊂ P := by
  rw [Finset.ssubset_iff_subset_ne]
  exact ⟨Finset.filter_subset ..,fun e => (Finset.mem_filter.mp (show v∈trim P v from e.symm ▸ hv)).2 le_rfl⟩
lemma remains (H:Crown P) {v:V} (h:v≠⊥) : Crown (trim P v) := by
  refine ⟨Finset.mem_filter.mpr ⟨H.base,fun e => h (le_bot_iff.mp e)⟩,
    Finset.Subset.trans (Finset.filter_subset ..) H.inner,fun {a b} e hb => ?_⟩
  obtain ⟨hb,hy⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨H.roots e hb,fun g => hy (g.trans e)⟩
lemma frontier_trim (H : Crown P) {v i : V} (h : v ≠ ⊥) (hv : v∈P) :
    i∈brim E (trim P v) ↔ i=v ∨ (i∈brim E P ∧ ¬ v ≤ i) := by
  constructor
  · intro hi; by_cases h' : i=v
    · exact Or.inl h'
    right; rw [on_brim] at hi; obtain ⟨hg,ho,hf⟩ := hi
    have hq : ¬ v ≤ i := fun e => (Finset.mem_filter.mp hf).2 (touch_par E (lt_of_le_of_ne e (Ne.symm h')))
    exact ⟨(on_brim ..).mpr ⟨fun a => hg (Finset.mem_filter.mpr ⟨a,hq⟩),ho,(Finset.mem_filter.mp hf).1⟩,hq⟩
  rintro (rfl|⟨hi,he⟩)
  · rw [on_brim]; have hf := from_par E h
    exact ⟨fun e => (Finset.mem_filter.mp e).2 le_rfl,h,Finset.mem_filter.mpr ⟨H.roots hf.le hv,hf.not_ge⟩⟩
  rw [on_brim] at *
  exact ⟨fun e => hi.1 (Finset.mem_filter.mp e).1,hi.2.1,
    Finset.mem_filter.mpr ⟨hi.2.2,fun a => he (a.trans (par_le ..))⟩⟩

def glen (v : V) := (brim E P).filter (fun i => v ≤ i)
def shore (v : V) := (brim E P).filter (fun i => ¬ v ≤ i)

lemma glen_touch {v i:V} (hv:v∈P) (hi:i∈ glen E P v) : v ≤ par E i := by
  obtain ⟨hi,h⟩ := Finset.mem_filter.mp hi
  exact touch_par E (lt_of_le_of_ne h (fun e => ((on_brim ..).mp hi).1 (e ▸ hv)))
lemma glen_kids {v:V} (hv:Maximal (· ∈ P) v) : glen E P v = strictChildren E v := by
  ext1 i
  constructor
  · intro hi; have ht := glen_touch E P hv.1 hi
    obtain ⟨hi,h⟩ := Finset.mem_filter.mp hi; rw [on_brim] at hi
    exact (kid_mem E).mpr ⟨lt_of_le_of_lt ht (from_par E hi.2.1),le_antisymm (hv.2 hi.2.2 ht) ht⟩
  intro h; rw [kid_mem] at h
  refine Finset.mem_filter.mpr ⟨(on_brim ..).mpr ⟨fun e => h.1.not_ge (hv.2 e h.1.le),
    bot_lt_iff_ne_bot.mp (lt_of_le_of_lt bot_le h.1),by rw [h.2]; exact hv.1⟩,h.1.le⟩
omit [Fintype V] in
/-- Non-amputated nonroot internal. -/
def rest := P.erase (⊥:V)
omit [Fintype V] in
lemma rest_mem {i:V} : i∈ rest P ↔ i≠⊥ ∧ i∈P := Finset.mem_erase

omit [Fintype V] in
lemma bud_possible (h : (rest P).Nonempty) : ∃ v:V, v∈rest P ∧ Maximal (· ∈ P) v := by
  obtain ⟨v,hv⟩ := (rest P).exists_maximal h
  obtain ⟨h0,hV⟩ := Finset.mem_erase.mp hv.1
  exact ⟨v,hv.1,hV,fun {w} hw e => hv.2 (Finset.mem_erase.mpr ⟨bot_lt_iff_ne_bot.mp
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr h0) e),hw⟩) e⟩

def bud (h : (rest P).Nonempty) := (bud_possible P h).choose
omit [Fintype V] in
lemma bud_mem (h : (rest P).Nonempty) : bud P h∈rest P := (bud_possible P h).choose_spec.1
omit [Fintype V] in
lemma bud_live (h : (rest P).Nonempty) : bud P h∈P := (Finset.mem_erase.mp (bud_mem ..)).2
omit [Fintype V] in
lemma bud_trunk (h : (rest P).Nonempty) : bud P h≠⊥ := (Finset.mem_erase.mp (bud_mem ..)).1
omit [Fintype V] in
lemma bud_tip (h : (rest P).Nonempty) : Maximal (· ∈ P) (bud P h) := (bud_possible P h).choose_spec.2
lemma tiny (hP : Crown P) (h : ¬ (rest P).Nonempty) : glen E P ⊥=strictChildren E ⊥ ∧ brim E P=strictChildren E ⊥ := by
  have hp : Maximal (· ∈ P) (⊥ : V) := ⟨hP.base,fun {a} ha _ => le_bot_iff.mpr
    (Classical.byContradiction fun e => h ⟨a,Finset.mem_erase.mpr ⟨e,ha⟩⟩)⟩
  rw [← glen_kids E P hp]; simp [glen]
end YM.OPE.Arboreal
