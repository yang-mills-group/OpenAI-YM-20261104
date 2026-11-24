import YM.OPE.Trunk.Spine
/-!
# Additional slots kept on the books

Collocated at origin. Explicit permission mask for interior/exterior joint choices,
also used in verifying spacing only on those choices. Implements backward requests
through the future tests (there is no distinguished projection for each anchor
*without* a reference price; always use this full allowance).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup
open scoped Topology BigOperators Classical ContDiff
variable {I J T Z V : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype Z][DecidableEq Z][Fintype V][DecidableEq V]{t u w b j k :ℕ}{Q: Rhythm I} (H:Fibers I J)
set_option quotPrecheck false
namespace Rhythm
variable (Z) (S': Type)
def booth (x:I→S') (y:Z→ S') := Sum.elim x y
variable {S'}
def walletF (H:Fibers I J) : Fibers (I⊕Z) (J⊕Z) where
    bunch:= Sum.map H.bunch id
    twig:= Sum.map H.twig id
    sectioned:= fun i=>by cases i with | inl i=> exact congr_arg Sum.inl (H.sectioned i) | inr=>rfl
def track (Q:Rhythm I)(M:I⊕Z→S') (t:ℕ)(i:Q.Panel t ⊕ Z) := M ((walletF Z (Q.fromAll t)).twig i)
variable {Z} (Q)
structure Host (t:ℕ) (P: I→ Z→Prop)(s:Ward (Names V (Q.Panel t ⊕ Z))) : Prop where
    pitch : Pitch s
    lens : Trial s
    single (v:V)(j i:Z): Drapery.room (s) (v,Sum.inr i) (v,Sum.inr j) → i=j -- use room
    permit (v:V) i (l:Q.Panel t): Drapery.room (s) (v,Sum.inl l) (v,Sum.inr i) → ∀ x:I,x∈Q.tribe l.val t→ P x i

variable {P:I→ Z→Prop}{s:Ward (Names V (Q.Panel t ⊕ Z))}
namespace Host
variable {Q}
lemma trans (h : Q.Host t P s)(e:t ≤ u) : Q.Host u P (pullback (walletF Z (Q.fold e)) s):=by
    let A:= walletF Z (Q.fold e); let Ω:= pullback A s
    refine ⟨h.pitch.group,trial _ _ h.lens,fun v i j he=>h.single v i j (Drapery.seats.1 he),fun v i j he k hv=>?_⟩
    let q:=(Q.fold e).bunch j
    have hp:= Drapery.seats.1 he; exact h.permit v i q hp k ((Q.arrives ..).2 (Q.conj (Q.swap (Q.matchs ..)) (Q.phase_low ((Q.arrives ..).1 hv) e)))
lemma acts (h:Q.Host t P s) {v:V}{x:Z}{p:Q.Panel t}(hh: Drapery.room s (v,.inl p) (v,.inr x)) : P p.val x:= h.permit v x p hh p.val ((Q.arrives ..).2 (Q.yes ..)) -- `..` syntax
end Host
lemma spent (Z:Type)(he:t ≤ u) {T:Type}(f:I→T)(g:Z→T) : track Z Q (Sum.elim f g) u ∘ (walletF Z (Q.fold he)).twig= track Z Q (Sum.elim f g) t:= funext fun i=> by cases i <;> rfl
lemma ceiling (Z:Type)[Fintype Z][DecidableEq Z] (t:ℕ) : Fintype.card (Q.Panel t ⊕ Z) ≤ Fintype.card I+ Fintype.card Z:=by rw [Fintype.card_sum]; exact add_le_add_left (Drapery.card_size (Q.fromAll t)) _ -- add side name

-- copy payment
variable (Z)
lemma mapped (e:t ≤ u) (l:Q.Panel t) : (walletF Z (Q.fold e)).contents (.inl l)=( (Q.fold e).contents l).image Sum.inl:=by
    ext x; rw [Fibers.focuses,mem_image]; simp_rw [Fibers.focuses]; cases x <;> simp [walletF]
lemma solo_c (he:t≤u) (l:Z): (walletF Z (Q.fold he)).Solo (Sum.inr l):=by
    rintro (k|k) hk; · cases hk
    exact congr_arg _ (Sum.inr.inj hk).symm
lemma peer_solo (he:t ≤ u) (l:Q.Panel t)(hk:(Q.fold he).Solo l): (walletF Z (Q.fold he)).Solo (.inl l):=by rintro (k|k) ht; exact congr_arg _ (hk k (Sum.inl.inj ht)); cases ht
-- trans.Combine
lemma transShape (h:t≤u) : Drapery.splitAt (walletF Z (Q.fromAll t)) (walletF Z (Q.fromAll u)) (walletF Z (Q.fold h)):=by rintro (k|k); exact congr_arg Sum.inl (Q.as_split h k); rfl
lemma transShape_panel (h:t≤u) (he:u≤w) : Drapery.splitAt (walletF Z (Q.fold (h.trans he))) (walletF Z (Q.fold he)) (walletF Z (Q.fold h)):=by rintro (k|k); exact congr_arg Sum.inl (Q.chain h he k).symm; rfl
end Rhythm
end YM.OPE.Log.Trunk
