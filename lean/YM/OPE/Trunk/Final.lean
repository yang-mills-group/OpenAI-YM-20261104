import YM.OPE.Trunk.Wax
/-!
# Heading on the root. Capture, invert AND compress all copies at once

Any layout and any prescribed reader bits. Erases the root mark, even
if already a complete signed discrepancy within. Alignment through k0
of this and the future matches is not thrown away.Factorization tests
then in physical normalization at any translated detector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Rhythm.Store
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station Cells
open Book.Tariff Playout.Rake
open scoped Topology BigOperators Classical ContDiff
variable {I J Z V : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype Z][DecidableEq Z][Fintype V][DecidableEq V]{G:Gauge}
    {H l m k b N p T t t' q d:ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {S:Q.Loom}{P:I→ Z→ Prop}{u:∀ i:ℕ,I→Site (C.side i p)}
    (U:Q.Tour C S b H N p u)
variable {W r D}(L:LogPackage C W r D)(h:C.Makes)
local notation "Θ"=> standC C b N p
local notation "Y"=> C.path.levels
local notation "Ξ"=> C.path.rep N p
local notation "K"=> C.path.levels.budget
local notation "i!"=> ((C.labels.level d).Index)
local notation "κ"=> Q.ticket Q.star 0
local notation "B"=> Site (C.side b p)
namespace Highest
open Studio Pigment Extra.Histories.Relay
abbrev finalScan (V:Type) (J:Type)[Fintype V][DecidableEq V][Fintype J][DecidableEq J](i:I) : Ward (Names V (I⊕J)):= clash (recognize i) (Ward.all (Names V I))
lemma oneHost (Q:Rhythm I) (V Z:Type)[Fintype V][DecidableEq V][Fintype Z][DecidableEq Z]: Q.Host 0 (fun _ _=>False) (finalScan V Z (Q.ticket Q.star 0)):=by
    let f:= recognize (J:=Z) (Q.ticket Q.star 0); let A:= sweep V f
    refine ⟨Pitch.clashAt f Pitch.all,crashTrials f (OPE.Log.Trial.all _),?_,?_⟩
    · rintro v j i ⟨w,hh,hL,hM⟩; obtain ⟨hw,hP⟩:= hh; exact Sum.inr.inj (congr_arg Prod.snd (hP hL hM (show A (v,.inr i)=A (v,.inr j) from rfl)))
    rintro v i l ⟨m,⟨hx,hh⟩,hm,hs⟩; have he:= Q.unity l; have hw:= hh hm hs (show A (v,.inl l)=A (v,.inr i) from congr_arg (fun k=>(v,k)) he); cases hw
local notation "F"=> (C.labels.level d)
local notation "f'"=> Q.TypeAt i!
local notation "Q'"=> walletF i! (Q.fold (Nat.zero_le 1))
local notation "G'"=> finalScan B i! (Q.ticket Q.star 0)
local notation "b!"=> S.below 0
variable {c:ℕ}{φ:Q.TypeAt (C.labels.level d).Index 1→ℕ}{p₀:Finset (Q.TypeAt (C.labels.level d).Index 0)} {A: ℕ→ Q.TypeAt (C.labels.level d).Index 1→ℝ}{x:ℕ→ℝ}
    {g:Extra.Histories.Music (C.labels.level d) C.path N p}
    {p₁ : Q.TypeAt (C.labels.level d).Index 1 → Config G (C.side N p)→ℂ}
    {Q₀:∀ i:ℕ,Q.TypeAt (C.labels.level d).Index 1 → Cup (C.path.rep N p i)}
    (S' : Case Q S L u N T 0 (fun _ _=>False) p₀ φ)
    (H': Ledger (standC C b N p) (laterEdge Q S N 1) (pullback (walletF (C.labels.level d).Index (Q.fold (Nat.zero_le 1))) (finalScan (Site (C.side b p)) (C.labels.level d).Index (Q.ticket Q.star 0))) p₁ Q₀ (motif (C.labels.level d).Index Q u 1) φ A (x 1) D)
local notation "v'"=> lineRelease Q' (A b!) (Sum.inl (Q.ticket Q.star 0))
local notation "Ω"=> provision L S T x 0
local notation "ν"=> transact L S T x 0
local notation "δ!"=> discharged L S T x 0 d
local notation "Ζ"=> (grouped_X p₁ (Q')) (Sum.inl (Q.ticket Q.star 0))
set_option quotPrecheck false
-- deliver payload at k0 horizon
include U h L S' H'
set_option maxHeartbeats 700000 in
lemma issue (hf:Stock.Tabs.opens C.path.levels 1 b q)(he:q ≤ S.below 0)(hk:C.ref 0 < b)(hq:C.ref d ≤ q)(hh: Sum.inl (Q.ticket Q.star 0)∉ p₀)
   (hG:G.Simple)(hr:Series C W (waybill (Y)) D N p d g)
   (hT : ∀ k: (C.labels.level d).Index, A (S.below 0) (Sum.inr k)= birthClock C (S.below 0) d 1 ∧ p₁ (.inr k)= C.O N p ((C.factory d N p).terminal (az g (S.below 0) k)) 0 ∧ Mantle C.path N p (S.below 0) (C.localSection d) (1,false) 0 ((g.tone (S.below 0)).plays (az g (S.below 0) k)) (Q₀ (S.below 0) (Sum.inr k))) :
    ∃ v:C.label d, Next.UVStress.quota C d b! N p v ≤ 2*stampOut C b! d (Ω*v') ∧ ∃ hi:b ≤ N, (center C.S p hi 0).rootTest (C.beta N p) (Ζ - C.O N p v 0) ≤ stakes C b q / road C b! d (δ! * v') q :=by
    let i:= S.below 0; let X:= Q.Panel 0; let Y':= (C.labels.level d).Index; let l:= Q.ticket Q.star 0; have hm(k)(ht:b ≤ k)(hh:k ≤ i): u k l.val=0:= U.spine 0 (Nat.zero_le _) l.val (Q.pinned_init _) k ht hh; let x' := afterWidth A i Q' p₀
    let p':=clash (recognize (J:=Y') l) (Ward.all (Names B X)); have hg:= oneHost Q (Site (C.side b p)) (C.labels.level d).Index; obtain ⟨Y₀,hY,hQ,hU⟩ := arrivesForm (d:=fun _=>d) (U:=U) L h S' H' hg hk hG (hD:=fun _ _=>hq.trans he)
    have hwF(k:Y'): Mantle C.path N p i (C.localSection d) (1,false) 0 ((g.tone i).plays (az g i k)) (Y₀ i (Sum.inr k)):=by rw [hQ (.inr k) (S'.onCrew k)]; exact (hT k).2.2
    let f:= grouped_X p₁ (walletF (C.labels.level d).Index (Q.fold (Nat.zero_le 1))); have hE(k:Y'): f (.inr k)= p₁ (.inr k):=by funext j; unfold f grouped_X; rw [show (walletF i! _).contents (.inr k)=_ from (Q.solo_c _ _ k).content,prod_singleton]; rfl
    have hQ'(j:Y'): afterWidth A i (walletF i! (Q.fold (Nat.zero_le 1))) p₀ i (.inr j)=birthClock C (S.below 0) d 1:= (if_pos (S'.onCrew j)).trans ((hT j).1)
    have he': x' i (.inl l)= v':= if_neg hh
    have hy:Cash ν:= ⟨hY.rate.1,hY.rate.2⟩; have hξ:= (Tariff.amounts (x:=x 1) L hG (T:=T) (show 0 < T from ((Fintype.card_pos_iff.mpr ⟨Q.star⟩)).trans_le ((Nat.le_add_right ..).trans S'.enough)) (⟨H'.rate.1,H'.rate.2⟩) (Q.belowLaunch S (Nat.zero_le _))).1; 
    have ht: 0 < x' i (.inl l):= hY.clock.ready (.inl l) i; have hXxi:= Tariff.eraseWidth (C:=C) (d:=d) (i:=S.below 0) (α:=x' i (Sum.inl l)) hy hξ ht; have hp : Lenient (near C.path.levels) (fun _:X=>i) (fun k (l:X)=> x' k (.inl l)):=by refine ⟨fun _ _=> hY.clock.ready .., fun a b h=> ?_, fun _ _=> hY.clock.paid ..⟩; have ha:a=l:= Q.unity a; subst a; change x' b _= _; unfold x' afterWidth; rw [if_neg hh,if_neg hh]
    obtain ⟨v,hv,hX,-⟩:= Mask.audition (y:=δ!) (x':=Ω*x' i (Sum.inl l)) L h l hY hf hk.le (φ:=fun _=> i) he le_rfl hG hq Pitch.all (OPE.Log.Trial.all X) (fun j h=>(h (Q.unity j)).elim) (fun m h ht=> hm m (hf.1.trans h) ht) (fun _=>rfl) (fun _ _ _=>rfl) hp (Tariff.erase_cash hy hξ|>.1.have_) (Tariff.erase_cash hy hξ|>.2) (fun j h he=>(by rw [le_antisymm he h,born_road])) (hU _ hh) hr (fun k=>⟨(hE k).trans (hT k|>.2.1),hwF k⟩) hXxi.2 (fun k=> hXxi.1.trans_eq (congr_arg _ (hQ' k).symm))
    refine ⟨v,?_,hf.1.trans (he.trans hY.limit),?_ ⟩
    · rw [← he']; exact hv
    rw [← he']; unfold applySign at hX; rw [if_pos rfl] at hX; exact hX
end Highest
end YM.OPE.Log.Trunk.Rhythm.Store
