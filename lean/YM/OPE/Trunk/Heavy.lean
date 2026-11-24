import YM.OPE.Trunk.Variant
/-! # Assess funds after erasure -/
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
local notation "κ"=> carried Q Z
local notation "R"=> walletF Z (Q.fold t.le_succ)
local notation "b!"=> S.below t
variable (U':Q.Strike H l)(φ:Z→ℕ)(v:I→ℝ)(w:ℕ→Z→ℝ)
local notation "Y"=> C.path.levels
local notation "v!"=> width Q S C v w
local notation "z!"=> patchWidth Q S C H l d v w
local notation "φ'"=>patchDues Q S Z l φ
lemma otherRates {i:Q.TypeAt Z t}(he:i≠ κ t) : z! t m i=v! t m i:= if_neg he
include L U'
lemma Account (hq:t = H) (he:C.ref d ≤ S.launch l)(hv:Lenient (near (Y)) (Plain.due Z Q S φ t) (width Q S C v w t))(hG:G.Simple) : Lenient (near (Y)) (φ' t) (z! t):=by
    subst t; have ht:= U'.before; have hp:= rootDue (Q:=Q) (S:=S) φ ht; have hy := (hv.ready (κ H)); have hz(m):z! H m (κ H)= road C (S.below H) d (estate H v (owner Q H)) (max m (S.launch l)):=by
       rw [patchWidth,if_pos rfl,if_pos ht,show Plain.width Q S C v w H m (κ H)=estate H v _ from piece_pay w v (issuanceAge U' le_rfl)] -- let rewrite?
    let i0:= S.launch l; let y:= estate H v (owner Q H); have hy':0 < y:= lt_of_lt_of_le (hy i0) (piece_pay (C:=C) (S:=S) w v (m:=i0) (issuanceAge U' le_rfl)).le
    refine ⟨fun i m=>?_,fun i m h =>?_,fun i m=>?_⟩
    · by_cases h:i= κ H; subst i; rw [hz]; exact road_art hy' _; rw [otherRates v w h]; exact hv.ready ..
    · by_cases hi:i=κ H; swap; · rw [no_gains φ hi] at h ⊢; rw [otherRates v w hi,otherRates v w hi]; exact hv.early i m h -- fix app syntax
      rw [hi,hp] at h ⊢; rw [hz,hz,max_eq_right h,max_self]
    by_cases hi:i= κ H; swap; · rw [otherRates v w hi,otherRates v w hi]; exact hv.paid ..
    rw [hi,hz,hz]; rcases lt_or_ge m (S.launch l) with h|h;
    · rw [max_eq_right h.le,max_eq_right (by omega : m+1≤_)]; exact mul_le_of_le_one_left (road_art hy' _|>.le) (inv_le_one_of_one_le₀ ((Y).fits.delayed (m+1)|>.le))
    rw [max_eq_left h,max_eq_left (h.trans m.le_succ)]; exact road_wealth L hG hy' (he.trans h)

omit L
lemma along_w (he:t < H) : z! t= afterWidth (z! (t+1)) b! (R) (keep Q Z l t):=by
    have hv: v! t=afterWidth (v! (t+1)) b! (R) (warmSet Z Q t):= wakeShape w v ((he.trans_le U'.atMost).le); have ht:=ownerAlive U' he.le Z; have he_:=fundingOrigin Q Z t.le_succ; funext m k; by_cases hm:k=κ t
    · subst k; have hm(j): lineRelease (R) (v! (t+1) b!) (κ t)= v! t j (κ t) := by rw [hv]; exact (if_neg ht).symm
      by_cases hp: l < t; swap
      · -- Spending at or beyond parent
        let w':= widen S C H l d; let k':=(R).contents (κ t); let j:= κ (t+1); have hx:j∈k':= (Fibers.focuses ..).2 he_
        have hf(i): z! (t+1) b! i= v! (t+1) b! i * (if i=j then w' else 1) := by
           by_cases hk:i=j; swap; · rw [if_neg hk,otherRates v w hk,mul_one]
           subst i; rw [if_pos (rfl : j=j),patchWidth,if_pos (rfl : j=j)]; split; next h=> rw [max_eq_right (show S.below t ≤ _ from (Q.belowLaunch S (he.trans_le U'.atMost).le).le.trans (S.mono Q (by omega) (U'.before.trans_le U'.atMost).le))]; rfl
           rfl
        let z':= Finset.prod k' (fun i=> if i=j then w' else 1); have hz:z'=w':=by simp [z',hx];
        rw [patchWidth,if_pos rfl,if_neg hp,afterWidth,keep,if_neg hp,if_neg ht]; unfold lineRelease; simp_rw [hf,prod_mul_distrib]; rw [show (∏ i∈ (R).contents (κ t),if i=j then w' else 1)=w' from hz]; exact congr_arg (· * w') (hm m).symm
      let p:= (R).contents (κ t)
      have hK':(R).Solo (κ t):= quietCrew U' hp he Z
      have hz := hK' _ he_; rw [patchWidth,if_pos rfl,if_pos hp,afterWidth,keep,if_pos hp, if_pos (mem_insert_self ..),hz,patchWidth,if_pos rfl,if_pos (hp.trans_le t.le_succ)]; congr 1; rw [← hm]; unfold lineRelease; rw [hK'.content,prod_singleton,hz] -- width m vs b! through H+? holds m not b; width at t+1 awake previously so constant from Plain.width defined; rw
      let i:= owner Q (t+1); change v! (t+1) b! (.inl i)=v! (t+1) m (.inl i); rw [piece_pay w v (issuanceAge U' he),piece_pay w v (issuanceAge U' he)] -- rewrite let
    have hh(i)(he:i∈(R).contents k):i ≠ κ (t+1):= fun h=>hm (((Fibers.focuses ..).1 he).symm.trans ((congr_arg _ h).trans he_))
    have h:k∈ keep Q Z l t ↔ k∈ warmSet Z Q t:=by
       unfold keep; split; · simp only [mem_insert,hm,false_or]
       rfl

    rw [otherRates v w hm,hv]; by_cases he:k∈warmSet Z Q t
    · rw [afterWidth,if_pos he,afterWidth,if_pos (h.mpr he),otherRates v w (hh _ ((Fibers.focuses ..).2 ((R).sectioned _)))]
    rw [afterWidth,if_neg he,afterWidth,if_neg (mt h.mp he)]; exact (prod_congr rfl (fun i hi=> otherRates v w (m:=b!) (hh i hi))).symm -- orientation
end Variant
end YM.OPE.Log.Trunk.Rhythm.Store
