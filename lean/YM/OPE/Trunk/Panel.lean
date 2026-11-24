import YM.OPE.Laying.Holding
/-!
# Finite ultrametric pattern data

In descending heights, use distinct *layers* of captures
with super-(poly T) spacing jump between layers. A single pattern
can bring together multiple comparable heights in any geometry event.
This also deals with non-pair and unary events, and doesn't require a
special location for a given representative leaf in a cluster.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open scoped Topology BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    {i j k:I}{t u v : ℕ}
set_option quotPrecheck false
structure Rhythm (I:Type) where
    star : I
    limit : ℕ -- last nonempty layer included
    age : I→ℕ
    gap : I→I→ℕ
    bounded i:age i≤limit
    loose i j: gap i j ≤ age i
    flip i j: gap i j=gap j i
    fan i j k:min (gap i j) (gap j k) ≤ gap i k
variable (Q:Rhythm I)
namespace Rhythm
section
omit [Fintype I] [DecidableEq I]
def phase (t:ℕ)(i j:I):Prop:= i=j ∨ t≤ Q.gap i j
lemma phase_age (h: t ≤ Q.age i) : Q.phase t i i:= Or.inl rfl -- unused
lemma yes (t:ℕ)(i:I):Q.phase t i i:= Or.inl rfl
lemma swap (h: Q.phase t i j): Q.phase t j i:= h.elim (fun h=>Or.inl h.symm) (fun h=> Or.inr (Q.flip i j ▸ h))
lemma conj (h:Q.phase t i j)(he:Q.phase t j k): Q.phase t i k:= h.elim (fun h=>h.symm ▸ he) (fun hv=> he.elim (fun h' => Or.inr (h' ▸ hv)) (fun hv'=> Or.inr ((le_min hv hv').trans (Q.fan ..))))
lemma phase_low (h:Q.phase u i j)(he:t ≤ u): Q.phase t i j:= h.elim Or.inl (fun h=>Or.inr (he.trans h))
lemma early (h : Q.phase t i j) (hv:t ≤ Q.age i) : t ≤ Q.age j:= h.elim (fun h=>h ▸ hv) (fun he=>(Q.flip i j ▸ he : t≤Q.gap j i).trans (Q.loose j i))
lemma behind (he : Q.age i < t) : Q.phase t i j↔ i=j:= ⟨fun h => h.resolve_right (fun h'=> not_lt_of_ge (h'.trans (Q.loose ..)) he), fun h=> Or.inl h⟩
lemma split (h:i≠j) : Q.phase t i j ↔ t≤ Q.gap i j:= ⟨fun he=>Or.resolve_left he h,Or.inr⟩
lemma upperAge (h : ¬ Q.phase t i j) : Q.gap i j < t := lt_of_not_ge (fun he=> h (Or.inr he))
lemma leaf_spaced (h: ¬ Q.phase (t+1) i j) : Q.gap i j ≤ t:=Nat.le_of_lt_succ (Q.upperAge h)
-- weight classes & canonical representative. Index only. no LinearOrder I allowed
end
instance decides (i j:I): Decidable (Q.phase t i j):= by unfold phase;infer_instance
def tribe (i:I)(t:ℕ): Finset I:= univ.filter (fun j=> Q.phase t i j)
lemma arrives (i j:I)(t): j∈ Q.tribe i t ↔ Q.phase t i j:= by simp [tribe]
def rank (I:Type)[Fintype I](i:I) := Fintype.equivFin I i
lemma elects (i:I)(t:ℕ): ∃ j, Q.phase t i j∧∀ k,Q.phase t i k→ rank I j ≤rank I k:=by obtain ⟨j,hj,hk⟩:= exists_min_image (Q.tribe i t) (rank I) ⟨i,(Q.arrives ..).2 (Q.yes ..)⟩; exact ⟨j,(Q.arrives ..).1 hj,fun k hi=> hk k ((Q.arrives ..).2 hi)⟩
def chief (i:I) (t:ℕ): I:= (Q.elects i t).choose
lemma votes (i:I)(t:ℕ): Q.phase t i (Q.chief i t)∧ ∀ j,Q.phase t i j → rank I (Q.chief i t) ≤ rank I j:= (Q.elects i t).choose_spec
lemma matchs (i:I)(t:ℕ): Q.phase t i (Q.chief i t):= (Q.votes ..).1
lemma chiefFor (h:Q.phase t i j) : Q.chief i t=Q.chief j t:= (Fintype.equivFin I).injective (le_antisymm ((Q.votes ..).2 _ (Q.conj h (Q.matchs j t))) ((Q.votes ..).2 _ (Q.conj (Q.swap h) (Q.matchs i t))))
lemma agrees (i j:I) t : Q.chief i t=Q.chief j t ↔ Q.phase t i j:=⟨fun h=> Q.conj (Q.matchs i t) (h.symm ▸ Q.swap (Q.matchs j t)),Q.chiefFor⟩
-- Careful defeq use explicit functions vs coercions
abbrev Panel (t:ℕ): Type := {i:I // Q.chief i t=i}
def ticket (i:I)(t:ℕ) : Q.Panel t:=⟨Q.chief i t,(Q.chiefFor (Q.matchs i t)).symm⟩
lemma valent (j:Q.Panel t) : Q.ticket j.val t=j:= Subtype.ext j.property
lemma seats (i j:I)(t:ℕ): Q.ticket i t=Q.ticket j t ↔ Q.phase t i j:= ⟨fun he=> (Q.agrees i j t).1 (congr_arg Subtype.val he),fun he=>Subtype.ext (Q.chiefFor he)⟩
def fromAll (t:ℕ) : Fibers I (Q.Panel t):= ⟨fun i=> Q.ticket i t,Subtype.val,Q.valent⟩
lemma plate (t:ℕ)(k : Q.Panel t) : (Q.fromAll t).contents k= Q.tribe k.val t:=by ext i; rw [Fibers.focuses,Q.arrives]; change Q.ticket i t=k↔ _; exact ⟨fun h=> Q.swap ((Q.seats ..).1 (h.trans (Q.valent k).symm)),fun h=> ((Q.seats ..).2 (Q.swap h)).trans (Q.valent k)⟩
lemma end_piece (h: Q.age i < t) : Q.chief i t=i:= ((Q.behind h).1 (Q.matchs i t)).symm
lemma unopened (h: Q.age i < t) : Q.tribe i t={i}:=by ext j; rw [Q.arrives,Q.behind h,mem_singleton,eq_comm]
lemma leader_stays (x: Q.Panel t) (he : t ≤ u) : Q.chief x.val u=x.val:= (Fintype.equivFin I).injective (le_antisymm ((Q.votes ..).2 _ (Q.yes u x.val)) ((show rank I x.val=rank I (Q.chief x.val t) from congr_arg _ x.property.symm).trans_le ((Q.votes x.val t).2 _ (Q.phase_low (Q.matchs x.val u) he))))
-- the principal representative in a descendant sub-class is the same if it exists at this layer
lemma chief_up (he:t ≤ u)(hp:Q.phase u i (Q.chief i t)): Q.chief i u=Q.chief i t:=(Q.chiefFor hp).trans (Q.leader_stays (Q.ticket i t) he)

def fold (h:t ≤ u): Fibers (Q.Panel u) (Q.Panel t):= ⟨fun i=>Q.ticket i.val t,fun j=> ⟨j.val,Q.leader_stays j h⟩,Q.valent⟩
lemma fold_ticket (h:t ≤ u) (i:I): (Q.fold h).bunch (Q.ticket i u)=Q.ticket i t:= (Q.seats ..).2 (Q.swap (Q.phase_low (Q.matchs i u) h))
lemma chain (h:t ≤ u) (he:u≤v)(i: Q.Panel v) : (Q.fold h).bunch ((Q.fold he).bunch i)=(Q.fold (h.trans he)).bunch i:= Q.fold_ticket h i.val
lemma as_split (h:t ≤ u): Drapery.splitAt (Q.fromAll t) (Q.fromAll u) (Q.fold h):=fun i=>(Q.fold_ticket h i).symm
lemma lower_age (h:t ≤ u) (j:Q.Panel u): let i:= (Q.fold h).bunch j; t≤ Q.age i.val ↔ t ≤ Q.age j.val := (by intro i; exact ⟨Q.early (Q.swap (Q.matchs j.val t)),Q.early (Q.matchs j.val t)⟩)
lemma notBorn (h:t ≤ u){hp:Q.Panel t}(hi: Q.age hp.val < t): (Q.fold h).Solo hp:=fun j hj=> Subtype.ext ((Q.behind hi).1 (Q.swap ((Q.seats ..).1 (hj.trans (Q.valent _).symm))))
lemma unity (j:Q.Panel 0): j= Q.ticket Q.star 0:= (Q.valent j).symm.trans ((Q.seats ..).2 (Or.inr (Nat.zero_le _)))
lemma warmed (i:I){x : Q.Panel t}(hp:x.val∈ Q.tribe i t) : Q.chief i t=x.val:= (Q.chiefFor ((Q.arrives ..).1 hp)).trans x.property
end Rhythm
end YM.OPE.Log.Trunk
