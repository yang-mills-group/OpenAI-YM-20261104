import YM.OPE.Trunk.Panel
/-!
# Launch / feed and landing

Also support indicated origin through a spine step (so one interior
vertex can be matched additionally and priced on this same layout).
Root prices set at that same origin, comparisons to root requested center
then at continuum. Every marker on the spine has a longer shelf-life.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open scoped Topology BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    {i j k:I}{t u v b q H : ℕ}{Q:Rhythm I}
namespace Rhythm
variable (Q)
structure Loom where
    below : ℕ→ℕ
    launch : ℕ→ℕ
    stair t:t ≤ Q.limit → below t+1 < launch t
    upper t:t < Q.limit → launch t < below (t+1)
variable (S:Loom Q)
section
omit [Fintype I] [DecidableEq I]
lemma launch_down (h:t < u)(he:u ≤ Q.limit): S.launch t < S.below u:=by
    induction u with
    | zero=>omega
    | succ u IH=> rcases eq_or_lt_of_le (show t ≤ u by omega) with ht|ht
                  · rw [ht]; exact S.upper u he
                  exact ((IH ht (u.le_succ.trans he)).trans (Nat.lt_of_succ_lt (S.stair u (u.le_succ.trans he)))).trans (S.upper u he)
lemma belowLaunch (h:t ≤ Q.limit): S.below t < S.launch t:= (Nat.lt_of_succ_lt (S.stair t h)) -- name
lemma Loom.le_below (h:t ≤ u)(he:u ≤ Q.limit): S.below t≤ S.below u:= (h.lt_or_eq).elim (fun h=> ((belowLaunch Q S (h.le.trans he)).trans (launch_down Q S h he)).le) (fun h=> h ▸ le_rfl)
lemma Loom.less (h:t < u)(he:u ≤ Q.limit): S.launch t< S.launch u:= (launch_down Q S h he).trans (belowLaunch Q S he)
lemma Loom.mono (h:t ≤ u)(he:u ≤ Q.limit):S.launch t≤S.launch u:= (h.lt_or_eq).elim (fun h=>(S.less Q h he).le) (fun h=> h ▸ le_rfl)
lemma Loom.up_b (he:t ≤ Q.limit): S.below 0 < S.launch t:=lt_of_le_of_lt (S.le_below Q (Nat.zero_le _) he) (belowLaunch Q S he)
end
-- assembling gap after.Longer life. root-centered optional spine c.R
variable (H)
def focus (t:ℕ): Finset I:= Q.tribe Q.star t
lemma on_focus : i∈ Q.focus t ↔ Q.phase t Q.star i:=Q.arrives ..
def pinned (i:I)(t:ℕ):Prop:= t≤H ∧ i∈Q.focus t
variable {H}
lemma pinSame (he : Q.pinned H i u)(hp:t ≤ u)(h : Q.phase t i j) : Q.pinned H j t:= ⟨hp.trans he.1,(Q.on_focus).2 (Q.conj (Q.phase_low ((Q.on_focus).1 he.2) hp) h)⟩
lemma pinAge (he: Q.pinned H i t)(hp: H ≤ Q.age Q.star): t ≤ Q.age i:= Q.early ((Q.on_focus).1 he.2) (he.1.trans hp)
lemma at_star : Q.pinned H Q.star 0:=⟨Nat.zero_le _,(Q.on_focus).2 (Q.yes ..)⟩
lemma pinned_init (i : I) : Q.pinned H i 0:= ⟨Nat.zero_le _,(Q.on_focus).2 (Or.inr (Nat.zero_le _))⟩
structure Strike (H u:ℕ) : Prop where
    before : u < H
    exists_ : Q.age Q.star = H
    cut i : i∈ Q.focus H → Q.age i=H
    reserve i : i∉ Q.focus H → Q.gap i Q.star ≤ u
namespace Strike
variable {Q} (X:Q.Strike H u)
include X
lemma atMost : H ≤ Q.limit:= X.exists_ ▸ Q.bounded _
lemma here (i) (hp:i∈ Q.focus H) : Q.phase H i Q.star:= Q.swap ((Q.on_focus).1 hp)
lemma ageMembers (hp:i ∈ Q.focus H)(ha: Q.phase H i j): j∈ Q.focus H:= (Q.on_focus).2 (Q.conj ((Q.on_focus).1 hp) ha)
lemma follows (h:u < t)(he:t ≤ H)(i:I) : Q.pinned H i t ↔ i∈ Q.focus H:=by
    refine ⟨fun hp=>?_, fun hp=> ⟨he,(Q.on_focus).2 (Q.phase_low ((Q.on_focus).1 hp) he)⟩⟩; by_contra hh; have hy:= Q.swap ((Q.on_focus).1 hp.2); rcases hy with hy|hy -- hs syntax
    · exact hh (hy.symm ▸ ((Q.on_focus).2 (Q.yes ..)))
    exact h.not_ge (hy.trans (X.reserve _ hh))
lemma noother (h:u < t)(he:t ≤ H) : Q.focus H=Q.focus t:=by ext i; exact (X.follows h he i).symm.trans (by simp only [pinned,he,true_and])
lemma live_through (h:u < t)(he:t ≤ H) : Q.chief Q.star t=Q.chief Q.star H:= by
    let x:= Q.chief Q.star t; have hp : x ∈ Q.focus H  := (by rw [X.noother h he]; exact (Q.on_focus).2 (Q.matchs ..)); exact (Q.chief_up he ((Q.on_focus).1 hp)).symm
-- no need to wake between u and H
lemma quorum (he:u < t)(ht:t ≤ v)(hv:v ≤ H)(k:Q.Panel t)(hp:k=(Q.ticket Q.star t)) : (Q.fold ht).Solo k:=by
    subst k; intro i hi; let j:=i.val; apply Subtype.ext; change Q.chief Q.star t=j
    have hh:j ∈ Q.focus t:=(Q.on_focus).2 ((Q.seats _ _ t).1 (show Q.ticket _ t=Q.ticket j t from hi.symm)); rw [← X.noother he (ht.trans hv),X.noother (he.trans_le ht) hv] at hh
    change _ = i.val; exact (X.live_through he (ht.trans hv)).trans ((X.live_through (he.trans_le ht) hv).symm.trans (Q.warmed Q.star hh))
end Strike
end Rhythm
end YM.OPE.Log.Trunk
