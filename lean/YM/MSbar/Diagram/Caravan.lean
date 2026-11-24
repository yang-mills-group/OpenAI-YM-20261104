import YM.MSbar.Diagram.Native
/-! Natural open sites for shuffling reports with joint constraint. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Diagram
open Super Domain Domain.DR Loops Dim Symbol Function Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {C:Type}{E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U:Set ℂ} {m i j:ℕ}
abbrev Twins (C:Type)(m:ℕ):= Words C m × Words C m
abbrev together (w:Twins C m):= channel w.1+channel w.2=0

def pack (C:Type): Site (Twins C) := {
   toMotion := Motion.prod (line C) (line C)
   plot := fun f=> Domain.Plot _ _ _ (Prod.fst ∘ f) ∧ Domain.Plot _ _ _ (Prod.snd ∘ f) ∧ ∀ x,together (f x)
   views := fun h=> by intro p hp; exact ⟨h.1.refine p hp,h.2.1.refine p hp,fun x=> h.2.2 (p x)⟩
   size_up := fun V=> by intro E i1 i2 i3 x h; refine ⟨(h.1.passage (L:=V)),h.2.1.passage (L:=V),fun v=>?_⟩; change channel ((line C).move V (x v).1) +channel ((line C).move V (x v).2)=_; rw [quiet_move,quiet_move,← map_add,h.2.2 v,map_zero] }
variable {F:Record (Twins C)}
local notation "Λ" => (arena C)

def walk (p:C→Bit)(F:Record (Twins C)):Functionals C:=fun z m v=> split (p ∘ label) (fun x y=> F z m (x,y)) v
-- Deck technique extend Tame
structure Gem (C E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (m:ℕ) where
   a:C
   f:E→ Hat m
   g:E→ Mom m
   F:f.HasTemperateGrowth
   G:g.HasTemperateGrowth
namespace Gem
def pay (x:E)(q: Gem C E m):Letter C m:=((q.a,q.f x),q.g x)
theorem plot (v:List (Gem C E m)):Domain.Plot E C m (fun x=> v.map (pay x)) := by induction v with | nil=> exact Domain.Plot.empty | cons a v ih=> exact Domain.Plot.cons _ _ _ a.F a.G ih
theorem derives {f : E→Words C m} (h:Domain.Plot E C m f) : ∃ v:List (Gem C E m), f=fun x=>v.map (pay x) :=by
   induction h with
   | empty => exact ⟨[],rfl⟩
   | cons c t k h hh ht ih=> obtain ⟨v,rfl⟩:=ih;exact ⟨⟨c,t,k,h,hh⟩::v,rfl⟩
end Gem
-- transfer with arbitrary index T
lemma bet_split {T : Type} {p:T→ Bit}{F:ℂ→E→ Super.word T→ Super.word T→ℂ}
   (v:Super.word T)(h:∀ u w,(u++w).Perm v→ Bet U j (fun p:ℂ× E=> F p.1 p.2 u w)) : Bet U j (fun x:ℂ× E=> split p (F x.1 x.2) v):=by
     induction v generalizing F with
     | nil=> simp_rw [split_nil];exact h [] [] List.Perm.rfl
     | cons a v ih=> simp_rw [split_next]; exact (ih (F:=fun z x u w=> F z x (a::u) w) (fun u w he=> h _ _ (he.cons a))).add (ih (F:=fun z x u w=> sign (p a) (oddity p u)*F z x u (a::w)) (fun u w he=> (h _ _ (List.perm_middle.trans (he.cons a))).const_scale _))
lemma walk_cost (p:C→Bit)(hH:Eligible U j (pack C) F): Eligible U j Λ (walk p F):=by
   refine ⟨fun z hz ⦃i j⦄ L x=>?_,?_⟩
   · unfold walk; change split _ _ (x.map ((letters C).move L))=_; rw [splitting (p ∘ label) (p ∘ label) ((letters C).move L) (fun i=>rfl)]; refine split_change _ (fun u w _=>?_); exact hH.natural z hz L (u,w)
   intro E i1 i2 i3 m x h
   obtain ⟨v,rfl⟩:= Gem.derives (show _ from h.1)
   unfold walk; simp_rw [splitting (p ∘ Gem.a) (p ∘ label) (Gem.pay _) (fun i=>rfl)]; refine bet_split (F:=fun z w x y=> F z m (List.map (Gem.pay w) x,List.map (Gem.pay w) y)) v ?_
   intro x y he; refine hH.ev E (fun z:E=> (x.map (Gem.pay z),y.map (Gem.pay z))) ⟨Gem.plot _,Gem.plot _,fun z=>?_⟩
   unfold together; dsimp only; exact Eq.trans (by rw [← channel_plus,← List.map_append,channel_move (he.map _)]) (h.2 z)
-- derive One preserved under split
lemma one_split {p : Prop}{T:Type} (q:T→Bit) (F:E→Super.word T→Super.word T→ℂ)(v:Super.word T) (h:∀ u w,(u++w).Perm v→ Dim.One p (fun t=> F t u w)): Dim.One p (fun t=> split q (F t) v):=by induction v generalizing F with
 | nil=> simp_rw [split_nil]; exact h [] [] List.Perm.rfl
 | cons a v ih=> simp_rw [split_next]; exact (ih (fun t u w=> F t (a::u) w) (fun u w ht=> h _ _ (ht.cons a))).add (ih _ (fun u w hh=> (h _ _ (List.perm_middle.trans (hh.cons a))).scale _))

-- enough first
theorem color {W:Edition C}{d:Bit} {F:Series (Letter C m)} (he:Homogeneous (lift (W.binary m)) d F) (hp:∀ i p v, Dim.One (W.vector i) (fun t: Hat m=> F (((i,t),p)::v))) : Polar W F:=by
   intro i p u v; induction u using List.reverseRecOn generalizing v with
   | nil=> exact hp ..
   | append_singleton u a ih=>
      let f:=fun t:Hat m=>F (u++((i,t),p)::a::v); let s:=sign (W.parity (label a)) (W.parity i)
      have h : Dim.One (W.vector i) (s • f):= (ih (a::v)).scale s
      rw [show (fun t:Hat m=> F ((u++[a]) ++((i,t),p)::v))=s • f from ?_]; exact h
      funext t; rw [List.append_assoc]; exact he.commute u a ((i,t),p) v
end YM.MSbar.Diagram
