import YM.OPE.Compatible.Traces.Purchase
/-! Current maximal events simultaneously. Includes finishing at root. -/
set_option linter.unusedSectionVars true
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset
open scoped Topology Classical
variable {X:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X)
variable {Q:Finset X}{m:X→ℕ}
structure Series (P:Finset X) (m:X→ℕ):Prop where
    base : Crown P
    timing a b : a ≤ b→ b∈P→ m a ≤ m b
variable (Q m)
def whenHigh := Q.sup m
def bed : Finset X:= Q.filter fun i=>m i<whenHigh Q m
-- alternative border notation extends to ∅
def edge (Q:Finset X): Finset X:= if Q.Nonempty then brim D Q else {⊥}
def after (P:Finset X)(m:X→ℕ):= edge D (bed P m)
def buds := (after D Q m)∩Q
variable {Q m}(P: Series Q m)
namespace Series
include D P
lemma begun : Q.Nonempty := by
   cases D
   exact ⟨⊥, P.base.base⟩
lemma high {a:X}(h:a∈Q): m a≤ whenHigh Q m := by
   cases D
   cases P
   exact Finset.le_sup h
omit D
lemma dropped : bed Q m⊂ Q:=by
   obtain ⟨x,hx,hQ⟩:= Finset.exists_mem_eq_sup Q (show Q.Nonempty from ⟨⊥,P.base.base⟩) m
   rw [Finset.ssubset_iff_subset_ne]; refine ⟨Finset.filter_subset ..,fun he=>?_⟩
   have hh := (mem_filter.mp (show x∈bed Q m from he.symm ▸ hx)).2
   change m x < Q.sup m at hh; rw [hQ] at hh; exact lt_irrefl _ hh
lemma frame (h:(bed Q m).Nonempty): Series (bed Q m) m:=by
    obtain ⟨x,hx⟩:= h; have hv {u v:X}(h:u≤v)(hh:v∈bed Q m):u∈bed Q m:=
       Finset.mem_filter.mpr ⟨P.base.roots h ((mem_filter.mp hh).1),lt_of_le_of_lt (P.timing _ _ h (mem_filter.mp hh|>.1)) (mem_filter.mp hh|>.2)⟩
    exact ⟨⟨hv bot_le hx,(Finset.filter_subset ..).trans P.base.inner,hv⟩,fun a b h hb=>P.timing a b h (mem_filter.mp hb|>.1)⟩
include D
lemma birth {a:X}(h:a∈ after D Q m) : a∉bed Q m:=by
    cases P
    unfold after edge at h; split at h
    next he=>exact (on_brim D _|>.1 h).1
    next he=> rw [Finset.not_nonempty_iff_eq_empty.mp he]; exact notMem_empty _
lemma birth_stamp {a:X}(h:a∈buds D Q m) : m a=whenHigh Q m:= le_antisymm (high D P ((Finset.mem_inter.mp h).2)) (le_of_not_gt (fun he=> birth D P (mem_inter.mp h|>.1) (mem_filter.mpr ⟨(mem_inter.mp h).2,he⟩))) -- include
lemma spec {a:X}(h:a∈after D Q m)(hp:a∉Q): a∈brim D Q:=by
   unfold after edge at h;split at h
   next he=>
       obtain ⟨hx,hb,hk⟩:=(on_brim D _|>.1 h); exact (on_brim ..).mpr ⟨hp,hb,(mem_filter.mp hk).1⟩
   next he=> exact False.elim (hp ((mem_singleton.mp h) ▸ P.base.base))
lemma ancestor {x:X} (h:x∈brim D Q) : ∃ a∈after D Q m, a≤ x:=by
    by_cases he:(bed Q m).Nonempty
    · let S:= bed Q m; let F:(X→Prop):=fun v=> v∉S→ ∃ a∈brim D S, a≤v
      have hs:(bed Q m)=S:=rfl; have hh:after D Q m=brim D S:= if_pos he
      have ht (x:X): F x:= journey D (P:=F) (fun hp=>False.elim (hp ((frame P he).base.base))) (fun i hi ih hp=> by
           by_cases hk:par D i∈S
           · exact ⟨i,(on_brim D S|>.2 ⟨hp,hi,hk⟩),le_rfl⟩
           obtain ⟨a,hA,hq⟩:= ih hk; exact ⟨a,hA,hq.trans (par_le ..)⟩) x
      rw [hh]; exact ht x (fun hv=> (on_brim D Q|>.1 h).1 (mem_filter.mp hv|>.1))
    rw [after,edge,if_neg he]; exact ⟨⊥,mem_singleton_self _,bot_le⟩
lemma also_below {u:X}(hu:u∈ after D Q m):∃ x∈brim D Q, u ≤ x:=by
    by_cases hx:u∈Q
    · -- finite max descendant until leaf.Children need Q membership not generic. prove induction on >
       suffices hv : ∀ u∈Q,∃ x∈brim D Q, u ≤ x from hv u hx
       intro v; refine (Finite.wellFounded_of_trans_of_irrefl (α:=X) GT.gt).induction (C:=fun v=>v∈Q→∃ x∈brim D Q, v≤x) v ?_; intro a ih hz
       obtain ⟨b,hb⟩:= (kids_heart D).2 (P.base.inner hz); have hp:= (kid_mem ..).mp hb
       by_cases hB:b∈Q
       · obtain ⟨i,hi,hx⟩:= ih b hp.1 hB; exact ⟨i,hi,hp.1.le.trans hx⟩
       exact ⟨b,(on_brim D Q).mpr ⟨hB,bot_lt_iff_ne_bot.mp (lt_of_le_of_lt bot_le hp.1),hp.2 ▸ hz⟩,hp.1.le⟩
    exact ⟨u,spec D P hu hx,le_rfl⟩
def chief (x:brim D Q): after D Q m:=
   ⟨Classical.choose (ancestor D P x.2),(Classical.choose_spec (ancestor D P x.2)).1⟩
lemma reaches (x:brim D Q): (chief D P x).val ≤ x.val:= (Classical.choose_spec (ancestor D P x.2)).2
lemma crowns {x y:after D Q m}(h:x.val ≤ y.val):x=y:=by
   let S:= bed Q m; by_cases he:S.Nonempty
   · have hS:after D Q m=brim D S:= if_pos he
     apply Subtype.ext; by_contra hn; exact brim_apart D S (frame P he).base (hS ▸ x.2) (hS ▸ y.2) hn h
   have hS:after D Q m={⊥}:= if_neg he; rcases x,y with ⟨⟨x,hx⟩,y,hy⟩; exact Subtype.ext ((Finset.mem_singleton.mp (hS ▸ hx : x∈ ({⊥}:Finset X))).trans (Finset.mem_singleton.mp (hS ▸ hy : y ∈ ({⊥}:Finset X))).symm)

lemma chief_iff (x:brim D Q)(y:after D Q m): chief D P x=y ↔ y.val ≤ x.val:= ⟨fun e=>e ▸ reaches D P x,fun e=> (D.path (reaches D P x) e).elim (fun h=> crowns D P h) (fun h=>(crowns D P h).symm)⟩
lemma chef (x:after D Q m) : ∃ y:brim D Q,chief D P y=x:=by
   obtain ⟨y,he,hp⟩:= also_below D P x.2; exact ⟨⟨y,he⟩,(chief_iff D P _ x).2 hp⟩
def crease : Fibers ((brim D Q)⊕(buds D Q m)) (after D Q m) where
    bunch := Sum.elim (chief D P) (fun i=>⟨i.val, (Finset.mem_inter.mp i.2).1⟩)
    twig i:= if h:i.val∈Q then Sum.inr ⟨i.val,Finset.mem_inter.mpr ⟨i.2,h⟩⟩ else Sum.inl ⟨i.val,spec D P i.2 h⟩
    sectioned i := by
       dsimp only; split; rfl; next h=>exact (chief_iff D P _ i).mpr le_rfl
end Series
end YM.OPE.Arboreal
