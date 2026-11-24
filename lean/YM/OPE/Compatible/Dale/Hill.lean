import YM.OPE.Compatible.Dale.Dory
/-!
# Representatives. Choices throughout all layers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Weir
open Function Filter Lattice Laurent Tree Woody Finset
open scoped Topology BigOperators ComplexConjugate Classical
variable {E:Type*}
structure See (E:Type*) where
  go : Kv → E→E
  first (v:E): go 0 v=v
  last (k h : Kv)(v:E) : go (k+h) v= go k (go h v)
  fair (k:Kv)(h:k≠0)(v:E): go k v≠v
namespace See
variable (T: See E)
lemma together {i:E}{k h:Kv}(ht:T.go k i=T.go h i): k=h:=by
   by_contra hp; exact T.fair (h+k) (by intro he; rw [add_comm] at he; exact hp (neg_add_eq_zero.mp he)) i (by rw [T.last,ht,← T.last,twinned,T.first])
def club (i:E):= univ.image fun k : Kv=> T.go k i
lemma cards (i:E): (T.club i).card=4:=by
    rw [club,card_image_of_injective,card_univ,kvCard]; intro h k hk; exact T.together hk
lemma in_club (i:E): i∈ T.club i:=mem_image.mpr ⟨0,mem_univ _,T.first i⟩
lemma who {i j:E} : j∈ T.club i ↔ ∃ k,T.go k i=j:=by simp [club]
lemma clan (k:Kv)(i:E): T.club (T.go k i)=T.club i:=by
    ext j; rw [T.who,T.who]; constructor
    · rintro ⟨p,rfl⟩; exact ⟨p+k,T.last ..⟩
    rintro ⟨p,rfl⟩; exact ⟨p+k,by rw [← T.last,add_assoc,twinned,add_zero]⟩
lemma hare (i:E) : (T.club i).Nonempty:=⟨i,T.in_club i⟩
def chooseV (i:E): E:= Classical.choose (T.hare i)
lemma chosen (i:E): T.chooseV i∈ T.club i:= Classical.choose_spec (T.hare i)
@[simp] lemma chosen_at (k:Kv)(i:E): T.chooseV (T.go k i)= T.chooseV i:=by unfold chooseV; congr! 1; rw [T.clan]
@[simp] lemma twice (i:E): T.chooseV (T.chooseV i)=T.chooseV i:=by
   obtain ⟨k,h⟩:= T.who.mp (T.chosen i); nth_rw 1 [← h]; rw [T.chosen_at]
abbrev Seat:= {x:E // T.chooseV x=x}
def king (i:E): T.Seat:= ⟨T.chooseV i,T.twice i⟩
@[simp] lemma king_go (k:Kv)(i:E): T.king (T.go k i)=T.king i:=Subtype.ext (T.chosen_at k i)
@[simp] lemma king_here (p:T.Seat): T.king p.val=p:=Subtype.ext p.property
lemma joint (i:E): ∃ k,T.go k (T.king i).val=i:= by obtain ⟨k,h⟩:= T.who.mp (T.chosen i); exact ⟨k,by change T.go k (T.chooseV i)=i; rw [← h,← T.last,twinned,T.first]⟩
def tick (i:E):= Classical.choose (T.joint i)
lemma ticket (i:E): T.go (T.tick i) (T.king i).val=i:= Classical.choose_spec (T.joint i)
lemma tick_go (k:Kv)(i:E): T.tick (T.go k i)= k+ T.tick i:= T.together (i:=(T.king i).val) (by rw [T.last,T.ticket, ← T.king_go k i,T.ticket])
@[simp] lemma tick_here (p:T.Seat): T.tick p.val=0:= T.together (i:=(T.king p.val).val) (by rw [T.ticket,T.first,T.king_here])
def slash : E ≃ Kv × T.Seat :=⟨fun i=>(T.tick i,T.king i),fun p=> T.go p.1 p.2,T.ticket,by rintro ⟨h,i⟩; dsimp only; rw [T.tick_go]; simp⟩
lemma sumRep {M:Type*}[AddCommMonoid M][Fintype E](w:E→M)(h:∀ i k,w (T.go k i)=w i):
    ∑ i:E,w i=4 • ∑ p:T.Seat,w p:= calc
    _=∑ q: Kv × T.Seat, w (T.slash.symm q):=(Equiv.sum_comp T.slash.symm w).symm
    _=_:=by change (∑ q: Kv × T.Seat, w (T.go q.1 q.2.val))=_; simp only [h,Fintype.sum_prod_type,Finset.sum_const, card_univ,kvCard]
end See
variable {n:Side}(H:Even n.val)
-- dependent H

def sitesK (H:Even n.val): See (Site n):=⟨decks,flats,decks_plus H,vary_decks H⟩
def edgesK (H:Even n.val): See (edgeV n):=⟨ferry,ferry_0,ferry_plus H,ferry_free H⟩
end YM.OPE.Weir
