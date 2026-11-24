import YM.OPE.Trunk.Final
/-! # First actual root receipts in this budget (no auxiliary subtree matcher) -/
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
local notation "B"=> Site (C.side b p)
namespace Highest
open Studio Pigment Plain
abbrev roles (d:I→ℕ)(d':J→ℕ): I⊕ J→ℕ:= Sum.elim d d'
-- avoid cast
abbrev sumRole {M:ℕ→Type*}{d:I→ℕ}{d':J→ℕ}(x:(i:I)→ M (d i))(y:(i:J)→ M (d' i)) (i:I⊕ J): M (roles d d' i):= Sum.rec x y i
def labelsAll {d:I→ℕ}{d':J→ℕ}(x:(i:I)→ C.label (d i))(y:(i:J)→ C.label (d' i)) : (i:I⊕J)→ C.label (roles d d' i):= sumRole (M:=C.label) x y
def seals {d:I→ℕ}{d':J→ℕ}(x:(i:I)→ Music (C.labels.level (d i)) C.path N p)(y:(i:J)→ Music (C.labels.level (d' i)) C.path N p): (i:I⊕J)→Music (C.labels.level (roles d d' i)) C.path N p := sumRole (M:=fun d=>Music (C.labels.level d) C.path N p) x y
-- product formulas
lemma z_extra {d:I⊕J→ℕ}(v:(i:I⊕J)→ C.label (d i))(u:I→Site (C.side N p))(Q:Rhythm I)(i:J) : planWord C d N p v u Q t (.inr i)= C.O N p (v (.inr i)) 0:=by
   let U:=walletF J (Q.fromAll t); have hp:U.Solo (.inr i):=by rintro (k|k) hk; cases hk; exact congr_arg _ (Sum.inr.inj hk).symm
   funext g; unfold planWord grouped_X; rw [show U.contents (.inr i)= _ from hp.content,prod_singleton];rfl
lemma panel_z {d:I⊕J→ℕ} (v:(i:I⊕J)→ C.label (d i))(u:I→Site (C.side N p))(Q:Rhythm I)(i:Q.Panel t)(g) : planWord C d N p v u Q t (.inl i) g= ∏ j∈ Q.tribe i.val t, C.O N p (v (.inl j)) (u j) g:=by
   unfold planWord grouped_X; suffices hp : (walletF J (Q.fromAll t)).contents (.inl i)=(Q.tribe i.val t).image Sum.inl by rw [hp,prod_image (fun _ _ _ _ h=>Sum.inl.inj h)]; rfl
   rw [← Q.plate t i]; ext v; rw [Fibers.focuses,mem_image]; simp_rw [Fibers.focuses]; cases v <;>simp [walletF]
lemma group_later {d:I⊕J→ℕ} (v:(i:I⊕J)→ C.label (d i))(u:I→Site (C.side N p))(Q:Rhythm I) (he:t ≤ t'): grouped_X (planWord C d N p v u Q t') (walletF J (Q.fold he))=planWord C d N p v u Q t:= funext fun i=>funext fun g=> ((Q.transShape J he).group_prod ℂ (fun i=> past C d N p v (extras C (p:=p) (m:=N) J u) i g) i).symm
variable {g:Extra.Histories.Music (C.labels.level d) C.path N p}
abbrev basisUp (g: Extra.Histories.Music (C.labels.level d) C.path N p)(k:ℕ): (C.labels.level d).Index→ C.label d:= (C.factory d N p).terminal ∘ az g k
lemma swords {d:I→ℕ}{d':J→ℕ}{φ:I→ℕ}{φ':J→ℕ}{A:I→ℝ}{A':J→ℝ}{x:(i:I)→ C.label (d i)}{y:(i:J)→ C.label (d' i)}{g:(i:I)→ Music (C.labels.level (d i)) C.path N p}{g':(i:J)→Music (C.labels.level (d' i)) C.path N p} (h:Strands C L d φ A b N p x g)(h':Strands C L d' φ' A' b N p y g'): Strands C L (roles d d') (Sum.elim φ φ') (Sum.elim A A') b N p (labelsAll x y) (seals g g'):=by
   constructor <;> rintro (i|i)
   exacts [h.asset _,h'.asset _,h.wake _,h'.wake _,h.rooms _, h'.rooms _,h.live _,h'.live _,h.stamina _,h'.stamina _]
lemma forge (he: C.ref d≤ k)(h:b ≤ k)(hh:k ≤ N)(hq:Studio.Series C W (waybill (Y)) D N p d g) : Strands C L (fun _ : (C.labels.level d).Index=> d) (fun _=> k) (fun _=>1) b N p (basisUp (C:=C) g k) (fun _=>g):=⟨ fun _=> hq,fun _=>⟨h,hh⟩,fun _=>he,fun _=>one_pos,fun _=>(birthCounter L _ hq he hh).le⟩

variable (d':I→ℕ)(x:(i:I)→C.label (d' i)) (A:I→ℝ)(P':I→Site (C.side N p))
local notation "J'"=> ((C.labels.level d).Index)
local notation "E"=> (S.below 0)
local notation "z!"=> finalScan B J' (Q.ticket Q.star 0)
local notation "q!"=> walletF J' (Q.fold (Nat.zero_le 1))
abbrev base_price (Q:Rhythm I)(C:Family G)(S:Q.Loom) (d':I→ℕ)(A:I→ℝ): ℝ:=∏ i:I,birthClock C (S.launch (Q.age i)) (d' i) (A i)
variable {x':ℕ→ℝ}{Y':Finset ℕ}(hR:Rates S L T Y' x')
local notation "α"=> base_price Q C S d' A
local notation "Ω"=> provision L S T x' 0
local notation "ϑ" => discharged L S T x' 0 d
-- P for range at t0. positive plate constraints. Root Clark for plain only.
include U L h hR
set_option maxHeartbeats 1200000 in
lemma receipts (hf:Stock.Tabs.opens C.path.levels 1 b q)(he:q ≤ S.below 0)(hk:C.ref 0 < b)(hq:C.ref d ≤ q)(hG:G.Simple)(ht: Fintype.card I+ Fintype.card (C.labels.level d).Index ≤ T)
   (hF:∀ m,S.below 0 ≤ m →T ≤ r m)(hS:∀ i,A i>0)(hV:∀ i,C.ref (d' i) ≤ S.launch (Q.age i))(hQ:∀ i, Next.UVStress.quota C (d' i) (S.launch (Q.age i)) N p (x i) ≤ A i) :
    ∃ v:C.label d, Next.UVStress.quota C d E N p v ≤ 2*stampOut C E d (Ω*α) ∧ ∃ hi:b ≤ N, (center C.S p hi 0).rootTest (C.beta N p) ((fun Z=>∏ j,C.O N p (x j) (u N j) Z)-C.O N p v 0) ≤ stakes C b q / road C E d (ϑ * α) q:=by
    have hb := hf.1; have hz0:= S.up_b Q (Nat.zero_le Q.limit); have hm:S.below 0 ≤ N:= hz0.le.trans (U.lasts (Nat.zero_le Q.limit)).le; have hV'(i): S.launch (Q.age i) ≤ N:= (U.lasts (Q.bounded i)).le; choose g' hg using fun i=> Studio.seriesExist (p:=p) L.system ((hV i).trans (hV' i)); obtain ⟨g,hg'⟩:= Studio.seriesExist (p:=p) L.system ((hq.trans he).trans hm)
    let q₀:= E; let q' := Q.ticket Q.star 0; let K':= (J'); let i:=Q.limit+1; let W₀: I⊕K'→ℝ:= Sum.elim A (fun _=> 1); let f:= basisUp (C:=C) g q₀; let t:=roles d' (fun _:K'=>d); let v:=labelsAll (C:=C) x f; let g':= seals (C:=C) (d':=(fun _:K'=>d)) g' (fun _=>g); let φ (_:K'):= q₀
    let X:= Q.TypeAt K' 1; let ψ:= due K' Q S φ; let Y₀:= showAt Q S C φ W₀ t; let F:= planWord C t N p v (u N) Q; have hH: Strands C L t (origin Q S φ) W₀ b N p v g':= swords L ⟨hg,fun i'=>⟨(hb.trans he).trans (S.up_b Q (Q.bounded i') |>.le),hV' _ ⟩,hV,hS,hQ⟩ (forge L (hq.trans he) (hb.trans he) hm hg')
    have hiv:= oneHost Q (Site (C.side b p)) K'; let s:= pullback (q!) (z!); obtain ⟨X',hA,hY⟩:= Plain.upper (s₀:=s) U L h hH (hiv.trans (Nat.zero_le 1)) hR (by omega) ht hk hG hF (fun l _ hm i=> S.le_below Q (Nat.zero_le _) hm) (fun _ _ _ _ _ _ _ _ h=> h.elim); let t_:= warmSet K' Q 0
    obtain ⟨Z',hZ⟩:= no_sign (P:=fun _ _=>False) U L φ U.born (t:=0) (Nat.zero_le Q.limit) (fun _=> ⟨U.born,le_rfl⟩) ht hF (fun _ _ _ _ _ h=> h.elim) -- rename clash p
    have hP: Sum.inl q' ∉ t_:=mt ((warm_left K' Q q').1) (Nat.not_lt_zero _)
    have hv': lineRelease (q!) (Y₀ 1 q₀) (Sum.inl q')=α:=by
       have ht' : width Q S C (fun i'=>(birthClock C (S.launch (Q.age i')) (d' i') (A i'))) (earn C φ ((labelCost C (origin Q S φ) W₀ t) ∘ Sum.inr))=Y₀:=rfl
       have hp : estate 0 (fun i'=>birthClock C (S.launch (Q.age i')) (d' i') (A i')) q'=α:= estate_root ..
       have hA' : Y₀ 0 = afterWidth (Y₀ 1) q₀ (q!) t_:= wakeShape _ _ (Nat.zero_le _)
       rw [← hp, ← show Y₀ 0 q₀ (Sum.inl q')= estate (Q:=Q) 0 (fun i'=>birthClock C (S.launch (Q.age i')) (d' i') (A i')) q' from (piece_pay (C:=C) (S:=S) (m:=q₀) (i:=q') _ _ (Nat.zero_le _))] -- need explicit ty
       rw [hA']; exact (if_neg hP).symm
    have hC : grouped_X (F 1) (q!) (Sum.inl q')=(fun Z=>∏ i,C.O N _ (x i) (u N i) Z):=by funext Z; rw [show grouped_X (F 1) (q!) = F 0 from group_later ..,show F 0 (Sum.inl q') Z=_ from panel_z v (u N) Q q' Z, show Q.tribe q'.val 0= univ from eq_univ_of_forall (fun k=> (Q.arrives ..).2 (Or.inr (Nat.zero_le _)))]; rfl
    have hp_ (z:K'): Y₀ 1 q₀ (.inr z) = birthClock C (S.below 0) d 1 ∧ F 1 (.inr z)= C.O N _ ((C.factory d N p).terminal (az g q₀ z)) 0 ∧ Mantle C.path N p (S.below 0) (C.localSection d) (1,false) 0 ((g.tone q₀).plays (az g q₀ z)) (X' q₀ (.inr z)):=by
       refine ⟨earning_prev (x:= birthClock C (S.below 0) d 1) le_rfl, (z_extra ..),?_⟩; have hh' : (C.factory d N p).terminal.symm (basisUp (C:=C) g q₀ z)=az g q₀ z:= LinearEquiv.symm_apply_apply ..; rw [← hh']; exact hY z
    -- use alias word; rootTest type.T. let
    rw [← hC,← hv']; exact Highest.issue U L h Z' hA hf he hk hq hP hG hg' hp_
end Highest
end YM.OPE.Log.Trunk.Rhythm.Store
