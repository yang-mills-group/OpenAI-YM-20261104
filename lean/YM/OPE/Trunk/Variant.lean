import YM.OPE.Trunk.Rendezvous
/-! # After a signed erasure. Wider pressure capacities for the future groupings -/
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
open Plain Highest
abbrev owner (Q:Rhythm I)(t:ℕ):= Q.ticket Q.star t
abbrev carried (Q:Rhythm I)(Z:Type)(t:ℕ) : Q.TypeAt Z t:= Sum.inl (owner Q t)
local notation "t!"=> carried Q Z
local notation "R"=> walletF Z (Q.fold t.le_succ)
local notation "w!"=> warmSet Z Q
local notation "d!"=> due Z Q S
def keep (Q:Rhythm I)(Z:Type)[Fintype Z][DecidableEq Z] (l t:ℕ) := if l < t then insert (carried Q Z t) (warmSet Z Q t) else warmSet Z Q t
def patchDues (Q:Rhythm I)(S:Q.Loom)(Z:Type)[DecidableEq Z][Fintype Z](l:ℕ)(φ:Z→ℕ)(t:ℕ)(k:Q.TypeAt Z t):ℕ:= if k=carried Q Z t∧ l < t then S.launch l else due Z Q S φ t k
def widen (S:Q.Loom)(C:Family G)(H l d:ℕ):= (C.S.a (S.launch l)/ C.S.a (S.below H))^d
def patchWidth (Q:Rhythm I)(S:Q.Loom)(C:Family G)(t' l d:ℕ)(q:I→ℝ)(v:ℕ→Z→ℝ) (t m:ℕ)(i:Q.TypeAt Z t) := let p:=Plain.width Q S C q v t m i; if i=carried Q Z t then if l < t then road C (S.below t') d p (max m (S.launch l)) else p*widen S C t' l d else p
local notation "Y"=> C.path.levels
local notation "K"=> C.path.levels.budget
variable (U': Q.Strike H l)
lemma fundingOrigin (Q: Rhythm I) (Z:Type)[Fintype Z][DecidableEq Z](e:t ≤ t') : (walletF Z (Q.fold e)).bunch (carried Q Z t')=carried Q Z t:= congr_arg (Sum.inl (β:=Z)) (Q.fold_ticket e Q.star) -- Q star notation shadow!!
include U'
lemma issuanceAge (e:t ≤ H) : t ≤ Q.age (owner Q t).val:= Q.early (Q.matchs ..) (U'.exists_.symm ▸ e)
lemma ownerAlive (e:t ≤ H)(Z:Type)[Fintype Z][DecidableEq Z]: carried Q Z t ∉ warmSet Z Q t:= mt ((warm_left Z Q _).1) (not_lt.mpr (issuanceAge U' e))
lemma quietCrew (he:l < t)(ht:t < H)(Z:Type)[Fintype Z][DecidableEq Z]: (walletF Z (Q.fold t.le_succ)).Solo (carried Q Z t):= Q.peer_solo Z t.le_succ _ (U'.quorum he t.le_succ ht _ rfl)
lemma ownerIn {p:Q.Panel t} (ht:t≤H) : Q.phase t p.val Q.star↔ p=owner Q t:=⟨fun he=> (Q.valent p).symm.trans ((Q.seats ..).2 he),fun hy=> hy.symm ▸ Q.swap (Q.matchs ..)⟩
omit U'
variable (φ:Z→ℕ)(v:I→ℝ)(w : ℕ→Z→ℝ)
local notation "Φ"=> patchDues Q S Z l φ
lemma no_gains {i:Q.TypeAt Z t}(he:i≠t! t) : Φ t i=d! φ t i:= if_neg (fun h=> he h.1)
lemma wags (he:t≤l)(i:Q.TypeAt Z t) : Φ t i=d! φ t i:=if_neg (fun h=> he.not_gt h.2) -- not_gt? h.2
lemma rootDue (he:l < t) : Φ t (t! t)=S.launch l:=if_pos ⟨rfl,he⟩
include U h L U'
-- store branch.Preserve original counter clocks until needed
lemma tempCase (hP:t < H) (hφ:∀ z,b ≤ φ z∧ φ z≤S.below t) (hx:Fintype.card I+Fintype.card Z ≤ T) (he:∀ m,S.below 0 ≤ m → T ≤ r m) : ∃ H': Case Q S L u N T t (fun _ _=>False) (keep Q Z l t) (patchDues Q S Z l φ (t+1)), Plans H' b (Φ t) :=by
    let X:= keep Q Z l t
    have hu:= hP.trans_le U'.atMost
    obtain ⟨M,hM⟩:= Plain.no_sign (P:=fun _ _=>False) U L φ U.born hu.le hφ hx he (fun _ _ _ _ _ h=>h.elim)
    have hh:w! t ⊆ X:=by unfold X keep;split; exact subset_insert ..; exact fun _ h=>h -- undecl
    have hQ(i:Q.TypeAt Z t): i≠t! t → (i∈X↔i∈ w! t):=by
       intro hi; unfold X keep; split; next h=> simp [hi]
       rfl -- indentation
    have hs:(R).bunch (t! (t+1))= t! t:= fundingOrigin Q Z t.le_succ; have he':=ownerAlive U' hP.le Z; have hp':= issuanceAge U' hP.le; let y:= t! (t+1); let f:=(R).bunch
    by_cases ht:l < t
    · have hT: t! t ∈ X:= by unfold X keep; rw [if_pos ht]; exact mem_insert_self ..
      have hP': (R).Solo (t! t):= quietCrew U' ht hP Z; have hy:f (t! (t+1))=t! t:= hs
      have hx(i:Q.TypeAt Z (t+1))(he:i≠ t! (t+1)) : f i ≠ t! t:= fun h=> he ((hP' _ h).symm.trans (hP' _ hy))
      let hξ:= S.launch l; -- let
      have hR: Case Q S L u N T t (fun _ _=>False) X (Φ (t+1)):= by
         refine ⟨M.enough,M.tall,M.count,M.extra,fun i=>hh (M.onCrew i),fun i he=>M.owner i (fun h=>he (hh h)),?_,?_,?_⟩
         · intro i hi; by_cases he:i=t! t; subst i; exact hP'; exact M.single i ((hQ i he).1 hi)
         · intro i hi; by_cases he:i=t! (t+1)
           · rw [he,rootDue φ (ht.trans_le t.le_succ)]; exact (Q.launch_down S ht hu.le).le
           rw [no_gains φ he]; exact M.manual i ((hQ _ (hx _ he)).1 hi)
         intro i hi; have he:i≠t! (t+1):= fun he=> hi (by rw [he, hs]; exact hT); rw [no_gains φ he]; exact M.bleed i (fun h=>hi (hh h))
      refine ⟨hR, fun i=>?_,fun k hk=>?_,fun k hk=>?_,fun k hk=>?_⟩ -- Plan structure prop
      · by_cases hi:i=t! t
        · rw [hi,rootDue φ ht]; exact U.born.trans (S.up_b Q (ht.le.trans hu.le)).le
        rw [no_gains φ hi]; exact hM.fund _
      · by_cases he:k=t! t
        · rw [he,show (R).twig (t! t)= _ from hP' _ hs,rootDue φ ht,rootDue φ (ht.trans_le t.le_succ)]
        have ht:(R).twig k ≠ t! (t+1):= fun H=> he (((R).sectioned k).symm.trans ((congr_arg _ H).trans hs))
        rw [no_gains φ he,no_gains φ ht]; exact hM.terms _ ((hQ _ he).1 hk)
      · rw [no_gains φ (show k≠ t! t from (fun h=>hk (h.symm ▸ hT)))]; exact hM.max _ (fun h=>hk (hh h))
      rw [no_gains φ (show k≠ t! t from (fun h=>hk (h.symm ▸ hT)))]; exact hM.located _ (fun h=>hk (hh h))
    have ht': (Φ (t+1)) = d! φ (t+1):= funext (fun i=> by
        by_cases he:i=t! (t+1)∧ l < t+1; swap; · exact if_neg he
        obtain ⟨rfl,hζ⟩:= he -- <- subst? rfl but Eq.rec
        apply (rootDue φ hζ).trans; rw [price_due φ _,min_eq_right (show t≤ Q.age (owner Q (t+1)).val from t.le_succ.trans (issuanceAge U' hP))]; rw [show l=t from by omega])
    have he₀ : keep Q Z l t=w! t:= if_neg ht; rw [ht',he₀,(show Φ t=d! φ t from funext (fun i=> wags φ (by omega) i))]; exact ⟨M,hM⟩
end Variant
end YM.OPE.Log.Trunk.Rhythm.Store
