import YM.OPE.Compatible.Dale.Ledge
/-!
# A stand from a rooted tree in quotient
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory
open scoped Topology BigOperators ComplexConjugate Classical
variable {n c f:Side} (H:Even n.val)
-- quotient town
def Pond := Score.mk (foot H) (cap H)
def origin : Node H:= crumb H 0
def forward (d:Step)(x:Site n): Limb H × Bool:= (pathX H (d.used x), (d.neg).xor (dir H (d.used x)))
lemma stairs (d:Step)(x:Site n): (Pond H).start (forward H d x)=crumb H x ∧ (Pond H).lastV (forward H d x)=crumb H (x+d.vec):=by
   let f:=d.used x; obtain ⟨i,b⟩:=d; cases b
   · have hf:=descends H (x,i); have hh:=finale H (x,i); change (if false.xor (dir H (x,i)) then _ else _)=_ ∧ (if false.xor _ then _ else _)=_; change crumb H x=_ at hf; rw [Bool.false_xor]; constructor
     · exact hf.symm
     rw [Bool.false_xor]; exact hh.symm
   change (Pond H).start (pathX H (x-step i,i),true.xor _) =_ ∧ (Pond H).lastV (pathX H (x-step i,i),true.xor _)=crumb H (x+ -step i);rw [← sub_eq_add_neg]
   have hf:= descends H (x-step i,i); have hh:= finale H (x-step i,i); simp only [sub_add_cancel] at hh
   unfold Score.start Score.lastV Pond; dsimp only; change (if true.xor (dir H (x-step i,i)) then _ else _)=_ ∧ (if true.xor (dir H (x-step i,i)) then _ else _)=_ ; cases e:dir H (x-step i,i) <;>exact ⟨by simpa [e] using hh.symm,by simpa [e] using hf.symm⟩
open PertExtension.Orb in
def Seeks (x:Node H)(j:ℕ):Prop :=∃ (t:Site n)(w:Walk),crumb H t=x ∧ crumb H (stop t w)=origin H ∧ w.length=j
lemma seeker (x:Node H):∃ j,Seeks H x j:=by
   have ht:=PertExtension.Orb.arrival_end x.val; let w:=PertExtension.Orb.arrival x.val; refine ⟨_,x.val,reverse w,See.king_here ..,?_,rfl⟩; change crumb H _=crumb H 0; congr 1; nth_rw 1 [← ht]; exact reverse_stop w 0
-- rooted horizontal even if fixed gauge at zero chosen separately per level
def aimDepth (x:Node H):= Nat.find (seeker H x)
lemma hills_low (x:Node H)(hx:x≠origin H):∃ p:Limb H × Bool, (Pond H).start p=x ∧ aimDepth H ((Pond H).lastV p)<aimDepth H x:=by
   obtain ⟨t,w,h,hj,hy⟩:= (Nat.find_spec (seeker H x) : Seeks H x _); match w with
   | []=> exact (hx (h.symm.trans hj)).elim
   | d::w=>
     obtain ⟨ha,hv⟩:=stairs H d t; refine ⟨_,ha.trans h,?_⟩; have hz: aimDepth H _ ≤ w.length:= Nat.find_min' (seeker H ((Pond H).lastV (forward H d t))) ⟨_,w,hv.symm,hj,rfl⟩; unfold aimDepth at *; rw [← hy]; exact Nat.lt_succ_of_le hz
abbrev Plot := (Pond H).Stand ({origin H}: Set _)
def bramble : Plot H where
    point p:= Classical.choose (hills_low H p.val (p.property))
    root p:= (Classical.choose_spec (hills_low H p.val (p.property))).1
    flick := aimDepth H
    bump p:= (Classical.choose_spec (hills_low H p.val (p.property))).2
-- Vertical shapes from Tree.Arbitrary
variable (g:Ratio c f) (hp:Even c.val)(he:Odd g.count.val)
local notation "μ" => even_both g hp
abbrev LiftV (x:Node hp):Node μ:= crumb μ (g.embed x.val)
@[simp] lemma step_node (x:Site c): LiftV g hp (crumb hp x)=crumb μ (g.embed x):= by
      obtain ⟨i,h⟩:= (sitesK hp).joint x; let p := crumb hp x; change decks i p.val=x at h;change crumb μ (g.embed p.val)=_; rw [← h] -- likely
      rw [step_charm g hp]; exact ((sitesK μ).king_go i _).symm
lemma origin_step : LiftV g hp (origin hp)= origin μ:=by simp only [origin,step_node]; rw [← Ratio.root_embed,map_zero]
abbrev FollowV (x:Node μ):Node hp:= crumb hp (g.parent x.val)
include he
lemma parent_node (x:Site f): FollowV g hp (crumb μ x)=crumb hp (g.parent x):= by
      obtain ⟨i,h⟩:= (sitesK μ).joint x; let p := crumb μ x; change decks i p.val=x at h; change crumb hp (g.parent p.val)=_; rw [← h]
      rw [(step_parent g hp he ..).1]; exact ((sitesK hp).king_go i _).symm
lemma travel_v (x:Node hp): FollowV g hp (LiftV g hp x)=x:=by rw [LiftV,parent_node g hp he,Ratio.embed_parent]; exact See.king_here ..
-- bijection on internal
omit he in def Roots : Set (Node μ):= Set.range (LiftV g hp)
omit he in lemma root_foot (x:Site f): crumb μ x∈ Roots g hp ↔ ∃ y: Site c,x=g.embed y:=by
      constructor
      · rintro ⟨p,hp⟩; have hp:crumb μ (g.embed p.val)=crumb μ x:=hp; let k:=(sitesK μ).tick x; let j:=(sitesK μ).tick (g.embed p.val)
        refine ⟨decks (k+j) p.val,?_⟩; rw [step_charm g ‹Even c.val›]; have hj: decks j (crumb μ x).val=g.embed p.val:=by rw [←hp]; exact (sitesK _).ticket _
        have hr:= (sitesK μ).ticket x
        have he : decks (k+j) (g.embed p.val)=decks k (crumb μ x).val:= by rw [← hj,← decks_plus μ,add_assoc,twinned,add_zero]
        rw [he]; exact hr.symm
      rintro ⟨y,rfl⟩; exact ⟨crumb hp y,step_node g hp y⟩
omit he in lemma root_bud (x:Site f): crumb μ x∈ (Roots g hp)ᶜ ↔ leaf g x:=by
      rw [mem_compl_iff,root_foot]; unfold leaf; exact ⟨fun h e=>h ⟨_,e⟩,fun h ⟨k,hk⟩=> h (by nth_rw 2 [hk]; rw [g.embed_parent,hk])⟩
end YM.OPE.Cascade
