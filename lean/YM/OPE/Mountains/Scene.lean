import YM.OPE.Mountains.Portrait
/-! # Rhythm port ordering from a geometry tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset OPE.Log Mountain Trunk
open scoped Classical Topology BigOperators ContDiff
variable {I J:Type}[Fintype I] {s:Arboreal I} {φ:Ultrafilter J} {t:I→ℝ} {x:J→I→ E4}{R:J→I→ℝ}{M δ:ℝ}{i j k o u:I} {a b : Finset I}

section Find
-- LCA of any nodes (including same)
private lemma farm (s:Arboreal I) (i j:I) : ∃ k:I,s.Anc k i∧ s.Anc k j∧∀ u:I,s.Anc u i → s.Anc u j → s.Anc u k:=by
    let A:= univ.filter fun k=> s.Anc k i ∧ s.Anc k j; obtain ⟨k,hk,hv⟩:= A.exists_max_image s.depth ⟨s.root,mem_filter.mpr ⟨mem_univ _,s.closure _,s.closure _⟩⟩; obtain ⟨hp,hq⟩:= (mem_filter.mp hk).2; refine ⟨k,hp,hq,fun u hi hj=>?_⟩; by_contra hh
    exact (hv u (mem_filter.mpr ⟨mem_univ u,hi,hj⟩)).not_gt (((hi.compare hp).resolve_left hh).into (fun hu=>hh (hu ▸ Anc.same ..)))
def common (s:Arboreal I) (i j:I): I:= (farm s i j).choose
lemma span (s:Arboreal I) (i j:I) : s.Anc (s.common i j) i∧ s.Anc (s.common i j) j ∧ ∀ u:I,s.Anc u i → s.Anc u j → s.Anc u (s.common i j):= (farm s i j).choose_spec
lemma spans (s:Arboreal I)(i j:I): s.common i j=s.common j i:= ( (s.span j i).2.2 _ (s.span i j).2.1 (s.span i j).1).unique ((s.span i j).2.2 _ (s.span j i).2.1 (s.span j i).1)
lemma Fork.gca (h:¬ s.Anc i j)(hh:¬ s.Anc j i): s.Fork (s.common i j) i j:=by
    obtain ⟨hv,hp,hx⟩:= s.span i j; obtain ⟨v,he,hu⟩:= hv.first (show i≠ _ from fun hi=> h (hi.symm ▸ hp)); obtain ⟨v',he',hu'⟩:= hp.first (show j≠ _ from fun hj=>hh (hj.symm ▸ hv)); exact ⟨v,he,v',he',fun hz=> not_lt_of_ge (hx v hu (hz ▸ hu')|>.depth) (higher he),hu,hu'⟩ -- unique lca
lemma parentCommon (h:¬s.Anc i j)(hh:¬ s.Anc j i) : s.common i j = s.common (s.parent i) (s.parent j):=by
    let v:= s.common i j; have h':= Fork.gca h hh; have hp:= s.span (s.parent i) (s.parent j)
    exact (hp.2.2 v (h'.left.1.back h'.left.2) (h'.swap.left.1.back h'.swap.left.2)).unique ((s.span i j).2.2 _ (hp.1.joins (Anc.step s i)) (hp.2.1.joins (Anc.step s j)))
lemma Fork.link (h:¬s.Anc i j)(hh:¬ s.Anc j i) : s.Fork (s.common (s.parent i) (s.parent j)) i j:= by rw [← parentCommon h hh]; exact gca h hh
lemma inherits (hi:s.Anc o (s.parent i))(hj:s.Anc o (s.parent j)): s.common (s.parent i) (s.parent j)∈ s.tower o:= let hp:= s.span (s.parent i) (s.parent j); tower_at.mpr ⟨hp.1.inner (s.inward i),hp.2.2 o hi hj⟩
end Find

namespace Portrait
variable (h:s.Coterie (φ:Filter J) t M δ x R) (V:Portrait s φ R o)
    (ht:s.Active a)(ho:o∈a)(hb:b⊆ s.inputs a o) (r : b) -- members may be empty excluded
set_option quotPrecheck false
local notation "I'"=> (↑b:Type)
-- no mandatory nonempty if impossible
lemma tree_line (h:s.Coterie (φ:Filter J) t M δ x R) (hp:∀ i∈ b,s.Anc o (s.parent i))(i j k:I'):
    min (V.hue (s.common (s.parent i.val) (s.parent j.val))) (V.hue (s.common (s.parent j.val) (s.parent k.val))) ≤ V.hue (s.common (s.parent i.val) (s.parent k.val)):=by
    let f:=fun (i j:I')=> s.common (s.parent i.val) (s.parent j.val); have he(u v : I'):= s.span (s.parent u.val) (s.parent v.val); have hV(u v : I'): f u v∈ s.tower o:= inherits (hp _ u.property) (hp _ v.property)
    rcases ((he i j).2.1.compare (he j k).1) with hh|hh
    · exact le_trans (min_le_left ..) (adhere h V (hV i j) (hV i k) ((he i k).2.2 _ (he i j).1 (hh.joins (he j k).2.1)))
    exact le_trans (min_le_right ..) (adhere h V (hV j k) (hV i k) ((he i k).2.2 _ (hh.joins (he i j).1) (he j k).2.1))
-- internal helper. use hp not ht ho
variable (hp:∀ i∈ b,s.Anc o (s.parent i))
def frame : Rhythm I' where
    star := r
    limit := V.limit
    age i:= V.hue (s.parent i.val)
    gap i j:= V.hue (s.common (s.parent i.val) (s.parent j.val))
    bounded i:= V.bounded (tower_at.mpr ⟨s.inward _,hp _ i.property⟩)
    loose i j:= adhere h V (inherits (hp _ i.property) (hp _ j.property)) (tower_at.mpr ⟨s.inward _, hp _ i.property⟩) (s.span (s.parent i.val) _).1
    flip i j:= congr_arg V.hue (s.spans ..)
    fan:= tree_line V h hp -- order inspect
-- r first?
-- When rooted at the root of the whole placement, terminal i may be projected.
end Portrait
end YM.OPE.Arboreal
