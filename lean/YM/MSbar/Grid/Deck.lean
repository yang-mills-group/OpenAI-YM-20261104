import YM.MSbar.Grid.Snap

/-! Plot-convergence on a group, retaining labels and conservation even for continuous Fourier mass.
Will use for master identities & later pricing. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Function Finsupp Super Finset Filter Set MeasureTheory
open scoped BigOperators Classical Topology
variable {C M:Type*} [AddCommGroup M] [TopologicalSpace M] {G : ℕ→ AddSubgroup M} {w : ℕ→ℕ}

-- parameter index type independent of point dimension
structure Ticket (G:ℕ→AddSubgroup M)(w:ℕ→ℕ) where
   target : M
   f : ℕ→ M
   belongs (n): f n∈G (w n)
   tend : Tendsto f atTop (𝓝 target)
namespace Ticket
variable [IsTopologicalAddGroup M]

def negative (a:Ticket G w):Ticket G w:=⟨-a.target,fun n=> -a.f n,fun n=>(G _).neg_mem (a.belongs n), a.tend.neg⟩
def plus (a b:Ticket G w):Ticket G w:=⟨a.target+b.target,fun n=> a.f n+b.f n,fun n=>(G _).add_mem (a.belongs n) (b.belongs n), a.tend.add b.tend⟩
def none : Ticket G w:=⟨0,fun _=>0,fun _=>(G _).zero_mem,tendsto_const_nhds⟩
omit [IsTopologicalAddGroup M] in
def onward (a:Ticket G w)(u:ℕ→ℕ)(he:Tendsto u atTop atTop):Ticket G (w∘u):=⟨a.target,fun n=> a.f (u n),fun n=> a.belongs (u n), a.tend.comp he⟩
end Ticket

abbrev Deck (C:Type*)(G:ℕ→AddSubgroup M)(w:ℕ→ℕ):= List (C × Ticket G w)
namespace Deck
variable (u: Deck C G w)

def cap (l:Deck C G w):Field C M:=l.map fun x=>(x.1,x.2.target)
def see (l:Deck C G w)(n:ℕ):Field C M:= l.map fun x=>(x.1,x.2.f n)
def recover (u:Deck C G w){g:ℕ→ℕ}(h:Tendsto g atTop atTop): Deck C G (w∘g):= u.map fun x=> (x.1,x.2.onward g h)
theorem cap_recover {g:ℕ→ℕ}(h:Tendsto g atTop atTop):cap (recover u h)=cap u:=by rw [recover,cap,List.map_map]; rfl
theorem see_recover {g:ℕ→ℕ}(h:Tendsto g atTop atTop)(n:ℕ):see (recover u h) n=see u (g n):= by rw [recover,see,List.map_map]; rfl

variable [IsTopologicalAddGroup M]
def fee : Deck C G w → Ticket G w
    | [] => Ticket.none
    | a::l => a.2.plus (fee l)
theorem price (n:ℕ):channel (see u n)=(fee u).f n:=by induction u with | nil=> rfl | cons a u ih=> simp only [fee,Ticket.plus,see,List.map_cons,channel_cons]; congr! 1
theorem value : channel (cap u)=(fee u).target:= by induction u with | nil=> rfl | cons a l ih=> simp only [fee,Ticket.plus,cap,List.map_cons,channel_cons]; congr! 1
theorem report [T2Space M] (he:∀ n,channel (see u n)=0):channel (cap u)=0:=by
    simp_rw [price] at he; rw [value]; exact tendsto_nhds_unique (fee u).tend (funext he ▸ tendsto_const_nhds)
-- split geometry transport
end Deck

-- limit receipt on nested partitions
structure Copies (G:ℕ→AddSubgroup M)(F:ℕ→Amps C M)(f:Amps C M):Prop where
    clear(n): Quiet (F n)
    quiet: Quiet f
    pilots (w:ℕ→ℕ): Tendsto w atTop atTop → ∀ u:Deck C G w,(∀ n, channel (u.see n)=0) → Tendsto (fun n=> F (w n) (u.see n)) atTop (𝓝 (f u.cap))

-- Neutral lifts of a given word to decks. Need if proving ext identities in infinite volume.
variable [MeasurableSpace M] {μ:Measure M} (B:Snap M μ)
namespace Snap
variable [IsTopologicalAddGroup M]
omit [IsTopologicalAddGroup M] in
theorem take (u:Field C M)(h:Tendsto w atTop atTop): ∃ v:Deck C B.clan w,v.cap=u:=by
   induction u with
   | nil=>exact ⟨[],rfl⟩
   | cons a u ih=> obtain ⟨v,rfl⟩:=ih; exact ⟨(a.1,⟨a.2,fun n=>B.snap (w n) a.2,fun n=> B.mem ..,(B.seq _).comp h⟩)::v,rfl⟩
lemma ships (u:Field C M)(h:Tendsto w atTop atTop)(he:channel u=0): ∃ v:Deck C B.clan w,v.cap=u∧∀ n,channel (v.see n)=0:=by
   cases u with
   | nil=> exact ⟨[],rfl,fun _=>rfl⟩
   | cons a u=>
       rcases a with ⟨x,m⟩; obtain ⟨v,rfl⟩:=B.take u h; refine ⟨(x,v.fee.negative)::v,?_,fun n=> ?_⟩
       · rw [channel_cons,Deck.value] at he; exact congr_arg (fun z=> (x,z)::v.cap) (eq_neg_of_add_eq_zero_left he).symm
       rw [Deck.see,List.map_cons,channel_cons]; change -(Deck.fee v).f n+channel (Deck.see v n)=_; rw [Deck.price,neg_add_cancel]
end Snap

omit [MeasurableSpace M] in
lemma splitting {L T:Type*} (p:L→Bit)(q:T→Bit)(F:L→ T)(h : ∀ x,q (F x)=p x)(v:Super.word L)(w : Super.word T → Super.word T →ℂ): split q w (v.map F)=split p (fun x y=> w (x.map F) (y.map F)) v:=by
   induction v generalizing w with
   | nil=>simp [split_nil]
   | cons a v ih=> rw [List.map_cons,split_next,split_next,ih,ih]; simp_rw [List.map_cons,h,oddity, List.map_map,show q ∘ F=p from funext h]

-- sequenced split lemma without collision checking
lemma split_flow {α:Type*}(p:α→Bit){f:Super.word α→Super.word α→ℂ}{F:ℕ→Super.word α→Super.word α→ℂ}(v:Super.word α)
   (h:∀ x y,(x++y).Perm v → Tendsto (fun n=> F n x y) atTop (𝓝 (f x y))):
   Tendsto (fun n=>split p (F n) v) atTop (𝓝 (split p f v)):=by
    induction v generalizing f F with
    | nil => simpa using h [] [] List.Perm.rfl
    | cons a v ih=>
       simp_rw [split_next]; exact (ih (F:=fun n x y=>F n (a::x) y) (f:=fun x y=> f (a::x) y) (fun x y h'=> h _ _ (h'.cons a))).add (ih (F:=fun n x y=> sign (p a) (oddity p x)*F n x (a::y)) (f:=fun x y=> sign (p a) (oddity p x)*f x (a::y)) (fun x y h'=>tendsto_const_nhds.mul (h _ _ (List.perm_middle.trans (h'.cons a)))))
end YM.MSbar.Loops
