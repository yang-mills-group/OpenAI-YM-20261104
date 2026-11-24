import YM.OPE.Trunk.Yard
/-! # Stocks on raw positions (without a previous ERA) -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Rhythm.Store
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station
open Book.Tariff Playout.Rake
open scoped Topology BigOperators Classical ContDiff
variable {I J Z V : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype Z][DecidableEq Z][Fintype V][DecidableEq V]{G:Gauge}
    {H l m k b N p T t t':ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {S:Q.Loom}{P:I→ Z→ Prop}{u:∀ i:ℕ,I→Site (C.side i p)}
    (U:Q.Tour C S b H N p u)
variable {W r D}(L:LogPackage C W r D)(h:C.Makes)
local notation "Θ"=> standC C b N p
local notation "Y"=> C.path.levels
local notation "Ξ"=> C.path.rep N p
local notation "K"=> C.path.levels.budget
namespace Plain
open Extra.Histories.Relay
variable (Q S Z)
noncomputable def warmSet (t:ℕ) : Finset (Q.TypeAt Z t):= univ.filter (fun i=> Sum.elim (fun x:Q.Panel t=> Q.age x.val < t) (fun _=>True) i)
local notation "ϑ"=> Q.TypeAt Z
lemma warm_left (i: Q.Panel t): Sum.inl i∈ warmSet Z Q t ↔ Q.age i.val < t:= by simp [warmSet]
lemma warm_other (z:Z): Sum.inr z ∈ warmSet Z Q t:= by simp [warmSet]
-- due heights;
-- root t=0 already finished projection
noncomputable def due (φ:Z→ℕ) (t:ℕ)(i:Q.TypeAt Z t) := Sum.elim (fun i:Q.Panel t=> if t=0 then S.below 0 else S.launch (min (Q.age i.val) (t-1))) φ i
-- a layer back when unseen births.Due then simply earliest wake
-- use inspect
local notation "e!"=> (walletF Z (Q.fold t.le_succ))
local notation "Ψ" => due Z Q S
local notation "Γ" => (walletF Z (Q.fromAll t))
variable {Q S Z}(φ: Z→ℕ)
lemma price_due (i:Q.Panel (t+1)) : (Ψ φ (t+1) (Sum.inl i)) = S.launch (min (Q.age i.val) t):=by simp [due]
lemma rest_due {i:Q.Panel t}(he: t ≤ Q.age i.val) : Ψ φ t (Sum.inl i) = if ht:t=0 then S.below 0 else S.launch (t-1):=by
     unfold due; split_ifs <;> first|rfl| exact congr_arg S.launch (min_eq_right (by omega))
lemma due_unpaid {i:Q.Panel t}(he: Q.age i.val < t) : Ψ φ t (Sum.inl i)=S.launch (Q.age i.val):=by simp only [due, Sum.elim_inl]; rw [if_neg (by omega),min_eq_left (by omega)]
noncomputable def estate (t:ℕ) (q:I→ℝ) (p: Q.Panel t):= lineRelease (Q.fromAll t) q p
noncomputable def width (Q:Rhythm I)(S:Q.Loom)(C:Family G)(q:I→ℝ)(v:ℕ→Z→ℝ)(t:ℕ)(m:ℕ)(i:Q.TypeAt Z t):= Sum.elim (fun p:Q.Panel t=> if t ≤ Q.age p.val then estate t q p else earn C (S.launch ∘ Q.age) q m p.val) (v m) i
variable (B':ℕ→Z→ℝ)(q:I→ℝ)
local notation "Z'"=> width Q S C q B'
lemma piece_pay {i:Q.Panel t}(h: t ≤ Q.age i.val) : Z' t m (.inl i) = estate t q i:=if_pos h
lemma piece_steps {i : Q.Panel t}(h: Q.age i.val < t) : Z' t m (.inl i)= earn C (S.launch ∘ Q.age) q m i.val:=if_neg (not_le.mpr h)
lemma estate_leaf {i:Q.Panel t}(h: Q.age i.val < t) : estate t q i=q i.val:=by unfold estate lineRelease; rw [Q.plate t i,Q.unopened h,prod_singleton]
lemma estate_root (i:Q.Panel 0) : estate 0 q i= ∏ j,q j:=by unfold estate lineRelease; rw [Q.plate,show (Q.tribe i.val 0)=_ from eq_univ_of_forall (fun j=> (Q.arrives ..).2 (Or.inr (Nat.zero_le _)))]
lemma EstateM (h:t ≤ t')(k:Q.Panel t) : estate t q k=∏ i∈ (Q.fold h).contents k,estate t' q i:= by exact (Q.as_split h).group_prod ℝ q k
lemma wakeShape (ht:t ≤ Q.limit) : Z' t= afterWidth (Z' (t+1)) (S.below t) (e!) (warmSet Z Q t):=by
    funext i j; cases j with
    | inl j=>
       let A:=Q.fold t.le_succ; by_cases he:j.val∈(univ.filter (fun j:I=>Q.age j < t))
       · have hv:= (mem_filter.mp he).2; rw [afterWidth,if_pos ((warm_left Z Q _).2 hv),piece_steps B' q hv]; exact (piece_steps B' q (i:=A.twig j) (hv.trans t.lt_succ_self)).symm
       have hv:t ≤ Q.age j.val:= by_contra fun h=> he (mem_filter.mpr ⟨mem_univ _,lt_of_not_ge h⟩); rw [afterWidth, if_neg (mt (warm_left Z Q _|>.1) (not_lt.mpr hv)),piece_pay B' q hv, EstateM q t.le_succ]; unfold lineRelease; rw [Q.mapped Z t.le_succ _, prod_image (fun _ _ _ _ h=> Sum.inl.inj h)]; refine prod_congr rfl (fun k hk=> ?_)
       have hh:A.bunch k=j:= (Fibers.focuses ..).1 hk; have hx:t ≤ Q.age k.val:= (Q.lower_age t.le_succ k).1 (by change t ≤ Q.age (A.bunch k).val; rw [hh]; exact hv); rcases eq_or_lt_of_le hx with hK|hK; swap; · exact (piece_pay (S:=S) B' q (i:=k) hK).symm
       rw [piece_steps B' q (h:= show Q.age k.val < t+1 by omega), estate_leaf q (show Q.age k.val < t+1 by omega)] -- need earn at below t ≤launch (age).earning_prev even without Pos.
       exact (earning_prev (a:=near (Y)) (x:=q k.val) (m:=S.launch (Q.age k.val)) (k:=S.below t) (by rw [← hK]; exact (Q.belowLaunch S ht).le)).symm
    | inr j=> exact (if_pos (warm_other Z Q j)).symm
-- readiness affordability.Design X.Clock
include U in
lemma no_sign (hf:b ≤ S.below 0)(hP:t ≤ Q.limit)(hφ:∀ z,b ≤ φ z∧φ z ≤ S.below t) (hx:Fintype.card I+ Fintype.card Z ≤ T)
     (he: ∀ m:ℕ,S.below 0 ≤ m → T ≤ r m)(hS:∀ k,S.below t≤ k→ k ≤ N → ∀ i j,P i j→(K k).B^2 ≤ separation (u k i) 0) : -- replace
    ∃ H': Case Q S L u N T t P (warmSet Z Q t) (due Z Q S φ (t+1)), Plans H' b (due Z Q S φ t):=by
    have hK:= U.atleast hP
    let p₀:= warmSet Z Q t; have h(i:Q.Panel t):Sum.inl i∉p₀↔ t ≤ Q.age i.val:= (not_congr (warm_left Z Q _)).trans not_lt;
    have hV: Case Q S L u N T t P p₀ (Ψ φ (t+1)):= by
        refine ⟨hx,hP,he,hS,warm_other Z Q,fun i=> (h i).1,?_,?_,?_⟩
        · rintro (i|i) he; exact Q.peer_solo Z t.le_succ i (Q.notBorn _ ((warm_left Z Q i).1 he)); exact Q.solo_c Z t.le_succ i
        · rintro (i|i) hv; swap; · exact (hφ i).2
          have hc : ¬ t ≤ Q.age i.val:=by intro hc; exact ((h _).2 ((Q.lower_age t.le_succ i).2 hc)) hv
          have hx:=lt_of_not_ge hc; rw [price_due φ i, min_eq_left hx.le]; exact (Q.launch_down S hx hP).le
        rintro (i|i) hi; swap; · exact (hi (warm_other Z Q i)).elim
        rw [price_due φ i,min_eq_right ((Q.lower_age t.le_succ i).1 ((h _).1 hi))]
    refine ⟨hV,?_,?_,?_,?_⟩ -- structure Prop witness Lean cannot use in result? Exists proof, elimination
    · rintro (k|k); swap; · exact (hφ _).1
      unfold due; split; next he=> exact hf
      exact le_trans hf (S.up_b Q (le_trans (min_le_left ..) (Q.bounded _)) |>.le)
    · rintro (k|k) hk; swap; · rfl
      have hv:= (warm_left Z Q k).1 hk; rw [due_unpaid _ hv]; let p:=(Q.fold t.le_succ).twig k; change _ = Ψ φ (t+1) (Sum.inl p); rw [price_due, min_eq_left (show Q.age p.val ≤ t from hv.le)] <;> rfl
    · rintro (i|i) he; swap; · exact (he (hV.onCrew i)).elim
      have hk:= (h i).1 he; rw [rest_due φ hk]; split_ifs with h; · rw [h]
      exact (Q.launch_down S (by omega) hP).le
    rintro (i|i) he; swap; · exact (he (hV.onCrew i)).elim
    intro m hp h_m; have hk: t ≤ Q.age i.val:=(h i).1 he; rw [rest_due φ hk] at hp; split_ifs at hp with hx'; · rw [hx'] at h_m; omega
    obtain ⟨t,rfl⟩:= Nat.exists_eq_succ_of_ne_zero hx'; simp only [Nat.succ_sub_one] at hp; exact U.alumni t hP _ hk m hp h_m
end Plain
end YM.OPE.Log.Trunk.Rhythm.Store
