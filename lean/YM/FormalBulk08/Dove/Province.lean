import YM.FormalBulk08.Dove.Ego

/-! Numerical applicant. Costs only on structural arguments. No fields or
trajectory budget assumptions. `W` for formal Fk inputs; uses exactly same
K as underlying Levels. Ages include y/z admissibles. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster
open scoped Topology ENNReal BigOperators Classical
variable {X I:Type}{G:Gauge}{K:KernelChoices}{E:ℕ}
structure Empire (G:Gauge)(K:KernelChoices)(X:Type) where
    V:X→ Levels G
    kernel:∀ x,(V x).clock.kernel=K
    wood:∀ x i,Lodge ((V x).clock.op i 0).patch
namespace Empire
variable (W:Empire G K X) (x:X)
lemma bill (i:ℕ): ((W.V x).clock.op i 0).patch.Branches K G:= by have h:= ((W.V x).blocks i 0).branches;exact Eq.mp (congr_arg (fun k=> ((W.V x).clock.op i 0).patch.Branches k G) (W.kernel x)) h
end Empire
structure Lab (G:Gauge)(K:KernelChoices)(X:Type) extends Empire G K X where
    years:X→Time ℕ
    neck:X→ℕ
    width:X→ℕ→ℝ -- pre given
variable (W:Lab G K X)
namespace Lab
def scrolls : Page X:= ⟨fun i=>(W.V i).S,W.neck,W.years⟩
abbrev lower (i:Leaf W.scrolls):= (W.V i.a).clock.J i.b
abbrev upper (i:Leaf W.scrolls):= (W.V i.a).clock.J (i.b+1)
abbrev windowD (i:Leaf W.scrolls):= W.width i.a i.b
abbrev windowU (i:Leaf W.scrolls):=W.width i.a (i.b+1)
abbrev rootFee (i:Leaf W.scrolls)(E:ℕ):= cost0 G K (W.windowD i) (W.lower i) E
abbrev riseFee (i:Leaf W.scrolls)(E:ℕ):= cost0 G K (W.windowU i) (W.upper i) E
abbrev pat (i:Leaf W.scrolls) := ((W.V i.a).clock.op i.b 0).patch
abbrev demandL (i:Leaf W.scrolls)(ρ:ChartRatio G)(E:ℕ):= costL G K (W.windowU i) (W.windowD i) (W.rootFee i E) ρ (W.lower i) (W.upper i) E
abbrev callL (i:Leaf W.scrolls)(ρ:ChartRatio G)(E:ℕ):= labelC K (W.windowU i) (W.windowD i) (W.rootFee i E) ρ (W.lower i) E (W.pat i) (W.wood i.a i.b)

-- cards from block ratio
lemma residency (h:Years W.scrolls) : Soft (chron W.scrolls) (fun i=>(Fintype.card (Rim G (W.pat i)):ℝ)):= by
    have ht (L:Side): (Fintype.card (Site L):ℝ)=(L.val:ℝ)^4:= by simp [Site,Four,ZMod.card,Axis]
    convert (h.blocks.pows 4).times (soft_coin _ (Fintype.card (Loc G 1):ℝ)) using 1; ext1 i; change ((Fintype.card (_ × _)):ℝ)=_; simp only [Fintype.card_prod,Nat.cast_mul,ht];rfl
lemma board_price (h:Years W.scrolls):Soft (chron W.scrolls) (fun i=>(Fintype.card (Board G (W.pat i)):ℝ)):=by simpa [Board] using (W.residency h).plus (soft_coin _ (Fintype.card (Loc G 1):ℝ))
lemma slots_price (h:Years W.scrolls): Soft (chron W.scrolls) (fun i=>(Fintype.card (BoardL G (W.pat i) (W.wood i.a i.b)):ℝ)):= by
    apply (W.board_price h).below; intro i; simp only [Nat.abs_cast]; gcongr; change Fintype.card (_⊕_)≤Fintype.card (_⊕_); simp only [Fintype.card_sum]; apply Nat.add_le_add_right; exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
-- authored compatibility includes heading lookahead 1 even for last report; stated separately.
structure Use (ρ:ChartRatio G)(E:ℕ) :Prop where
    liable: Years W.scrolls
    haveJ: ∀ i, 5≤ W.upper i
    zero: ∀ i, 0<W.windowD i
    cost: ∀ i, W.windowD i ≤ window G K (W.lower i)
    pane: ∀ i, W.windowD i ≤ joint G K (W.lower i) (W.upper i)
    reserve: ∀ i, W.demandL i ρ E ≤ wideA i
    post: Soft (chron W.scrolls) (fun i=> W.callL i ρ E)
    structural: Soft (chron W.scrolls) (fun i=> W.rootFee i E)

lemma turn_quota {ρ:ChartRatio G}(h: Use W ρ E) (i): Flax G K.penalty (W.lower i) E (W.windowD i) (W.rootFee i E):= cost0_use ((W.V i.a).clock.adm i.b) (h.zero i) (h.cost i)
lemma turn_whose {ρ:ChartRatio G}(h:Use W ρ E)(i): Credentials K (W.lower i) (W.pat i) (W.wood i.a i.b) (W.windowU i) (W.windowD i) (W.rootFee i E) (W.callL i ρ E) ρ E:=
    label_cert K ρ (W.pat i) ((W.V i.a).clock.adm i.b) (h.haveJ i) (h.zero (stageFoot W.scrolls i 1)) (h.zero i) (h.pane i) (W.turn_quota h i).plus.le (h.reserve i) _

def wturn (g:I→ X): Lab G K I:= ⟨⟨W.V ∘ g,fun x=>W.kernel (g x),fun x=>W.wood (g x)⟩,W.years ∘ g,W.neck ∘ g,W.width ∘ g⟩
lemma observed {ρ:ChartRatio G}(h:Use W ρ E)(g:I→X):Use (W.wturn g) ρ E:= by
    let f(x: Leaf (W.wturn g).scrolls):= turnLeaf W.scrolls g x; exact ⟨h.liable.turn g, fun i=> h.haveJ (f i),fun i=>h.zero (f i),fun i=>h.cost (f i),fun i=> h.pane (f i),fun i=> h.reserve (f i), h.post.reach f,h.structural.reach f⟩
end Lab
end YM.FormalBulk08.Dove
