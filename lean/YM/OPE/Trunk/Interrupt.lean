import YM.OPE.Trunk.Hitch
/-! # Intermediary signed price. -/
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
namespace Variant
local notation "Θ"=> standC C b N p
local notation "Y"=> C.path.levels
local notation "K"=> C.path.levels.budget
local notation "J'"=> (C.labels.level d).Index
variable (U': Q.Strike H l)
    (S':Ward (Names (Site (C.side b p)) (Q.TypeAt Z H)))
    (h_H:Q.Host H (fun _ _=>False) S')
local notation "v'!"=> Q.TypeAt (Z⊕ J')
local notation "Q₁"=> spoil Q H S' J'
local notation "ξ"=> carried Q Z H
local notation "a"=> exchangeShape (Q.Panel H) Z J'
-- combine inherited extra with v-counter.
local notation "b!"=> S.below H
local notation "K₀"=> walletF (Z⊕ J') (Q.fold H.le_succ)
open Highest Plain Studio Pigment Extra.Histories.Relay
variable {F:Q.TypeAt (Z⊕(C.labels.level d).Index) (H+1)→ Config G (C.side N p)→ℂ}{F':∀ i:ℕ,Q.TypeAt (Z⊕(C.labels.level d).Index) (H+1)→Cup (C.path.rep N p i)} {g:Extra.Histories.Music (C.labels.level d) C.path N p}{x : ℕ→ℝ}{Y':Finset ℕ}
    {W₀:I→ℝ}{v:ℕ→Z→ℝ} {w:ℕ→ (C.labels.level d).Index→ℝ}{φ:Z→ℕ}
def augments (v:ℕ→Z→ℝ)(w:ℕ→J→ℝ)(k:ℕ) : Z⊕J→ℝ:= Sum.elim (v k) (w k)
def augGoal (φ:Z→ℕ)(J:Type)(q:ℕ): Z ⊕ J→ℕ:= Sum.elim φ (fun _=> q)
set_option quotPrecheck false
local notation "γ"=> augGoal φ J' b!
local notation "ϕ"=> due (Z⊕ J') Q S γ
local notation "w!"=> width Q S C W₀ (augments v w)
local notation "e!"=> estate H W₀ (owner Q H)
variable (hR:Rates S L T Y' x) (B' : Ledger (standC C b N p) (laterEdge Q S N (H+1)) (pullback (walletF (Z⊕(C.labels.level d).Index) (Q.fold H.le_succ)) (spoil Q H S' (C.labels.level d).Index)) F F' (motif (Z⊕(C.labels.level d).Index) Q u (H+1))
       (due (Z⊕(C.labels.level d).Index) Q S (augGoal φ (C.labels.level d).Index (S.below H)) (H+1)) (Plain.width Q S C W₀ (augments v w) (H+1)) (x (H+1)) D)
local notation "Ζ"=> grouped_X F K₀
local notation "z!"=> carried Q (Z⊕ J') H
local notation "Ω"=> provision L S T x H
local notation "δ'"=> discharged L S T x H d
local notation "y'"=> transact L S T x H
variable {p₀ :Finset (Q.TypeAt (Z⊕(C.labels.level d).Index) H)}
include h U U' B' h_H hR L
set_option maxHeartbeats 900000 in
lemma convoy_mid (hf:Stock.Tabs.opens C.path.levels 1 b q) (he:C.ref d≤ q)(hq:q ≤ S.below 0)(hk:C.ref 0 < b)(hG:G.Simple)(ht:d∈ Y') (hX : Series C W (waybill (Y)) D N p d g)
    (hQ':Case Q S L u N T H (film Q Z (C.labels.level d).Index H) (warmSet (Z⊕(C.labels.level d).Index) Q H) (due (Z⊕(C.labels.level d).Index) Q S γ (H+1))) (hJ:Plans hQ' b (ϕ H))
    (hy:∀ i:J', w (S.below H) i=birthClock C (S.below H) d 1 ∧ F (.inr (.inr i))= C.O N p ((C.factory d N p).terminal (az g b! i)) 0 ∧ Mantle C.path N p b! (C.localSection d) (1,false) 0 ((g.tone b!).plays (az g b! i)) (F' b! (.inr (.inr i)))):
    ∃ T': C.label d, Next.UVStress.quota C d b! N p T' ≤ 2*stampOut C b! d (Ω * e!) ∧ ∃ hi:b ≤ N,(center C.S p hi 0).rootTest (C.beta N p) (Ζ z! - C.O N p T' 0)≤ stakes C b q/(road C b! d (δ'* e!) q)∧
       ∃ X:∀ i:ℕ,Q.TypeAt Z H→ Cup (C.path.rep N p i), Ledger Θ (laterEdge Q S N H) S' (applySign d ((Ζ ∘(a).symm)∘Sum.inl) T' ξ) X (motif Z Q u H) (patchDues Q S Z l φ H) (patchWidth Q S C H l d W₀ v H) (x H) D ∧ ∀ k:Z,∀ i,X i (.inr k)=F' i (.inr (.inl k)):=by
    let z:= z!; let k:=ξ; let j:=S.below H; have hκ:= U'.before; have hs:=U'.atMost; have h_:= U.atleast hs; have hN:= (Q.belowLaunch S hs).trans (U.lasts hs); have he':q ≤ j:= hq.trans (S.le_below Q (Nat.zero_le _) hs); have hZ:= ownerAlive U' le_rfl (Z⊕ J'); let X(i):= motif (Z⊕ J') Q u H i; let d'(x: Q.TypeAt (Z⊕ J') H):ℕ:= if x=z then d else 0; let φ' :=ϕ H
    let f:=update φ' z j; have hf': f z=j:= update_self ..
    have hY: Plans hQ' b f:=by
       refine ⟨fun i=>?_,fun i h=>?_,fun i h=>?_,fun i h=>?_⟩
       · by_cases hi:i=z; subst i; exact hf'.symm ▸ h_; rw [show f i=φ' i from update_of_ne hi ..]; exact hJ.fund ..
       · have hi:i≠z:=fun hl=>hZ (show z∈ warmSet _ Q H from hl ▸ h); rw [show f i=φ' i from update_of_ne hi ..]; exact hJ.terms i h -- syntax
       · by_cases hi:i=z; subst i; exact hf'.le; rw [show f i=φ' i from update_of_ne hi ..]; exact hJ.max i h
       by_cases hi:i=z; subst i; · rw [hf']; intro i hi hm; exact (hm.not_ge hi).elim
       rw [show f i=φ' i from update_of_ne hi ..]; exact hJ.located i h
    have hV:= turnAbout S' (J') h_H; have hΛ(i): C.ref (d' i)≤ b!:=by unfold d'; split; exact he.trans he'; exact hk.le.trans h_
    obtain ⟨P',hP,hK,hL⟩:= Plans.pedant (d:=d') (U:=U) L h hQ' B' hV hY hk hG (fun i _=> hΛ i) (fun i ht _=>by rw [show i=z from by contrapose! ht; exact if_neg ht]; exact hf')
    let v':=w! H; let z':= warmSet (Z⊕J') Q H; let w':= width Q S C W₀ v H; have hK' : w! H=afterWidth (w! (H+1)) b! K₀ z':= Plain.wakeShape _ _ hs; let Ζ':= Ζ
    rw [← hK'] at hP hL
    have hy'(i)(j'): w! H i ((a).symm (.inl j'))= Plain.width Q S C W₀ v H i j':=by cases j' <;> rfl
    let w₁:= patchWidth Q S C H l d W₀ v H; let φ₁:=patchDues Q S Z l φ H
    have hp : Ledger Θ (S.below H) (clash (recognize k) S') (Ζ ∘(a).symm) (fun i=> P' i ∘(a).symm) (fun i=>X i ∘(a).symm) (f ∘(a).symm) (fun i=>v' i ∘(a).symm) y' D:= Mask.alteration h a hP (crashTrials (recognize k) h_H.lens) -- order check
    have hp'(l')(hl:l'≠k): f ((a).symm (.inl l'))= due Z Q S φ H l':=by
       have he:(a).symm (Sum.inl l')≠z:= fun h=> hl (Sum.inl.inj ((a).symm.injective (show (a).symm (.inl l')=(a).symm (.inl k) from h)))
       rw [show f _ = _ from update_of_ne he j φ']; cases l' <;> rfl
    have hϑ (m): v' m z=e!:= piece_pay _ W₀ (issuanceAge U' le_rfl)
    have hX_ : Lenient (near C.path.levels) φ₁ w₁:=by
       apply Variant.Account (t:=H) L U' φ W₀ v rfl (he.trans (hq.trans ((S.up_b Q (hκ.trans_le hs).le).le))) ?_ hG
       refine ⟨fun k' m=>?_,fun k' m hh=>?_,fun k' m=>?_⟩
       · rw [← hy' m k']; exact hP.clock.ready ..
       · by_cases hi:k'=k; · subst k'; rw [← hy' m,← hy' (due Z Q S φ H k)]; exact (hϑ _).trans (hϑ _).symm
         have h_m:= (hp' k' hi); rw [← h_m] at hh ⊢; rw [← hy' m,← hy' (f ((a).symm (.inl k')))]; exact hP.clock.early _ _ hh
       rw [← hy',← hy' (m+1)]; exact hP.clock.paid ..
    have hx:Cash y':=⟨hP.rate.1,hP.rate.2⟩; have hx':= (Tariff.amounts L hG (x:=x (H+1) ) (T:=T) (show 0 < T from ((Fintype.card_pos_iff.mpr ⟨Q.star⟩)).trans_le ((Nat.le_add_right ..).trans hQ'.enough)) (⟨B'.rate.1,B'.rate.2⟩) (Q.belowLaunch S hs)).1; have ht0:0 < e!:= (hP.clock.ready z j).trans_le (hϑ j).le
    have ht'(m) : w' m k=e!:= piece_pay _ W₀ (issuanceAge U' le_rfl)
    have hf_k: (a).symm (.inl k)=z:=rfl
    have ht_f(i:ℕ)(he:b ≤ i)(hf:i ≤ S.below H) :u i (Q.ticket Q.star H|>.val)=0:= U.spine H hs _ (show Q.pinned _ _ _ from ⟨le_rfl,(Q.on_focus).2 (Q.matchs ..)⟩) i (by assumption) (by assumption) -- add args!
    have hh:= Tariff.eraseWidth (C:=C) (d:=d) (i:=b!) hx hx' ht0
    have hXh : Minted C N p j d (Ω * e!) ((X j ∘ (a).symm) (.inl k)) ((P' j ∘ (a).symm) (.inl k)):=by
       rw [comp_apply,comp_apply,hf_k]; have he:= hL z hZ; rw [show d' z=d from if_pos rfl,show w! H b! z= _ from hϑ b!] at he; exact he
    have hEx(s:J'): let g₀:=((C.factory d N p).terminal (az g j s)); let l:=(a).symm (.inr s); (Ζ) l=C.O N p g₀ 0 ∧ Mantle C.path N p j (C.localSection d) (1,false) 0 ((g.tone j).plays (az g j s)) ((P' j ∘ (a).symm) (Sum.inr s)):=by
       intro g₀ l; have h_μ:l∈z':=hQ'.onCrew (.inr s); have he:(P' j l)=F' j (.inr (.inr s)):=hK _ h_μ j; refine ⟨?_,show Mantle C.path N p j (C.localSection d) (1,false) 0 ((g.tone j).plays (az g j s)) (P' j l) from (by rw [he]; exact (hy s).2.2)⟩ -- cast motif issue
       funext U; unfold grouped_X; rw [ (hQ'.single l h_μ).content,prod_singleton]; exact congr_fun ((hy s).2.1) U
    have hm: φ₁ k=S.launch l:= rootDue φ U'.before
    obtain ⟨T',hb,hΩ,M,h_M,hΛ⟩:= Mask.audition L h k hp hf hk.le (φ:=φ₁) (by rw [hm]; exact hq.trans ((S.up_b Q (hκ.trans_le hs).le).le)) (by rw [hm]; exact (Q.launch_down S hκ hs).le) hG he h_H.pitch h_H.lens (fun k' h=> (no_gains φ h).trans (hp' k' h).symm) (fun m h ht=>ht_f m (hf.1.trans h) ht) (fun _=>rfl) (fun i h j=>(otherRates W₀ v h).trans (hy' j i).symm) hX_ (y:=δ') (Tariff.erase_cash hx hx'|>.1.have_) (Tariff.erase_cash hx hx'|>.2)
      (fun i hi hs=>by rw [hm] at hi; change patchWidth Q S C H l d W₀ v H i k=_; rw [patchWidth,if_pos (show k=carried Q Z H from rfl),if_pos hκ,max_eq_left hi]; apply congr_arg (fun q=> road C (S.below H) d q i); exact (ht' i).trans (hϑ _).symm)
      hXh hX (fun k=> hEx k) (by change δ' * v' j z * _ * _ ≤ _; rw [hϑ]; exact hh.2) (fun x=>by have he:v' j ((a).symm (.inr x))=birthClock C j d 1:= (hy x).1; change δ' * v' j z* (2*stampOut C j d (Ω * e!)) ≤ y' * v' j _; rw [hϑ,he]; exact hh.1)
    refine ⟨T',hb,hf.1.trans (he'.trans hP.limit),?_,M,?_,?_⟩
    · change _ ≤ _; unfold applySign at hΩ; rw [if_pos rfl] at hΩ; rw [← hϑ j]; exact hΩ
    · let Y'':=Q.TypeAt Z H; have hX: motif Z Q u H = fun i=>(X i ∘(a).symm) ∘ Sum.inl:=funext fun i=>funext fun j=>by cases j<;>rfl
      rw [laterEdge,if_pos hs,hX]; exact h_M.thinner (hR.price H (hs.trans Q.limit.le_succ)|>.have_) (hR.salute H _ hs ht)
    exact fun i m => (hΛ (.inr i) (fun h:Sum.inr i=ξ => by cases h) m).trans (hK _ (hQ'.onCrew (.inl i)) m)
end Variant
end YM.OPE.Log.Trunk.Rhythm.Store
