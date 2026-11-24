import YM.OPE.Samples.Layout
/-!
# Tour via Lens: translations across heights
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Rhythm Function Filter Finset MeasureTheory Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Cells Motion Extra.Multi Next.Rank Station Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G}{I J Z:Type}[Fintype I][DecidableEq I]
    {H i m j n p b q t N:ℕ}{Q: Rhythm I} {S:Loom Q} {x:I→ Cover} {L:ℕ}
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "T"=> C.S.gridPoint
local notation "Ω"=> C.S.a
local notation "K"=> (Y).budget
local notation "L!"=> S.launch Q.limit
local notation "u!"=> T (L!) ∘ x
local notation "E"=> standC C b N p
-- Extend registration during tour
abbrev lens (C:Family G)(k p:ℕ)(x:I→ Cover)(m:ℕ)(i:I):= loops C k p (wrap (C.side k p) (x i)) m
namespace Canvas
variable  (U:Canvas S C H b x){y y':Cover}
variable {W r D}(L':LogPackage C W r D)
local notation "E'"=> Site (C.side b p)
local notation "Z"=> (fun p=> lens C (L!) p x)
local notation "η!"=> (fun i:ℕ=> C.S.toDepth (i.le_succ) p)
lemma no_steps (i:ℕ) : (Y|>.clock.op i p).ratio=η! i:=ratio_same ..
lemma empty_zero (h:j ≤ i)(p:ℕ): (C.S.toDepth h p).parent 0=0:=by let Z':=C.S.toDepth h p; nth_rw 1 [← show Z'.embed 0=0 from Z'.root.map_zero]; exact Z'.embed_parent _
lemma behind_zero (j m p:ℕ) : loops C j p (0:Site (C.S.side j p)) m=0:=by unfold loops; split; exact Ratio.root _|>.map_zero; exact empty_zero ..
include L' U
lemma native_cross (N:ℕ)(hp:i ≤ N)(ht:S.below 0 ≤ i)(hv:∀ j,Z p (S.below 0) j=0): Cross (K i).B ((standC C b N p).spectrum i (extras C (m:=i) (p:=p) Unit (Z p i))) :=by
    let z:= S.below 0; let u:= C.S.toDepth ht p; rintro ⟨j,q⟩ ⟨k,q'⟩ h; let F m:= ((standC C b N p).spectrum m (extras C (m:=m) (p:=p) Unit (Z p m))); let T' m:= Mix.camp C p b m;
    have he(x':Site (C.side b p))(q:I⊕ Unit) : u.parent (F i (x',q))= (C.S.toDepth U.born p).embed x':=by
       let y:= extras C (p:=p) (m:=i) Unit (Z p i); change u.parent (affine (hands C p b x').1 (Mix.camp C p b i x') (y q))= _; rw [elev C b p i (U.born.trans ht) x',embed_comp (C.S.toDepth U.born p) u _,Push.Local.parent_affine u (C.S.toDepth_odd ht p)]; cases q with
       | inl q=> rw [show u.parent (y (Sum.inl q))=0 from (again _ ht).trans (hv _ )]; simp [affine]
       | inr q=> rw [show u.parent (y (Sum.inr q))=0 from empty_zero ..]; simp [affine] -- inference again
    apply common_dist L' (F i (j,q)) (F i (k,q')) ht; rw [he,he,Station.both]; exact (U.horizon p).trans (Nat.le_mul_of_pos_right _ (separation_pos j k h))
set_option maxHeartbeats 800000 in
lemma pose : ∀ᶠ p in atTop, ∀ N> L!, Tour Q C S b H N p (Z p):=by
    let F:= Q.point H (u!); let P i:=priorL S i; choose y hy using (fun i hi j=>show ∃ y,_ from U.align i hi j)
    have hP(l)(he:l ≤ Q.limit): P l ≤ S.below l:= prior_le S he
    have hU(t)(ht:t ≤ Q.limit): S.below t +1 ≤ L! := (S.stair t ht).le.trans (S.mono Q ht le_rfl)
    have hL(t)(ht:t ≤ Q.limit)(i) : ∀ᶠ p in atTop, (C.S.toDepth (hU t ht) p).parent (wrap (C.side (L!) p) (x i))=(C.S.toDepth (show P t ≤ S.below t+1 from le_trans (prior_le S ht) (Nat.le_succ _)) p).embed (wrap (C.side (P t) p) (y t ht i)):=by
       have he : P t ≤ S.below t+1:=le_trans (prior_le S ht) (Nat.le_succ _)
       simp_rw [neighbor _ he]; refine proximity _ _ _ ?_; rw [zoom_grid,hy]; linarith only [U.closely t ht i,norm_nonneg (T (L!) (x i) - F i t)] -- norm defeq
    have hB(i j:I)(he:i ≠ j): ∀ᶠ p in atTop,(K (S.launch (Q.gap i j))).B^2+1 ≤ separation (Z p (S.launch (Q.gap i j)) i) (Z p (S.launch (Q.gap i j)) j):= bubbles _ _ (S.mono Q ((Q.loose i j).trans (Q.bounded i)) le_rfl) _ (U.spread i j he)
    filter_upwards [(eventually_all_finset (Iic Q.limit)).mpr (fun i h=> eventually_all.mpr fun ht:i ≤ Q.limit=> eventually_all.mpr fun j=> hL i ht j),eventually_all.mpr (fun i=>eventually_all.mpr (fun j=>eventually_all.mpr fun h:i≠j=> hB i j h)) ] with p hi hx N hn
    let h(i):= C.S.toDepth (Nat.le_succ i) p; let x' i:= Z p i
    have ht(t)(hl:t ≤ Q.limit)(i)(m)(he:P t ≤ m)(hv:m ≤ S.below t+1): x' m i=(C.S.toDepth he p).embed (wrap (C.side (P t) p) (y t hl i)) := custody he (hv.trans (hU t hl)) hv (hU t hl) (hi t (mem_Iic.mpr hl) hl i)
    have hf(t)(hl:t ≤ Q.limit)(i)(m)(he:m ≤ S.below t+1)(hp:Q.pinned H i t) : x' m i=0:=by
       have hu:= (zoom_inj C.S _ ((hy t hl i).trans ((Q.lead_zero hp _).trans (grid_zero C.S (P t)).symm))); rw [← show (C.S.toDepth he p).parent (x' _ i)=x' m i from again (wrap (C.side (L!) p) (x i)) he, ht t hl i (S.below t+1) (le_trans (hP t hl) (Nat.le_succ _)) le_rfl,hu,map_zero,show (C.S.toDepth _ p).embed 0= _ from Ratio.root (C.S.toDepth (show P t ≤ S.below t+1 from le_trans (hP t hl) (Nat.le_succ _)) p)|>.map_zero, empty_zero he] -- rw x' inside.? edit
    have hw(t)(hl:t ≤ Q.limit)(i)(m)(he:P t ≤ m)(hv:m ≤ S.below t) : x' (m+1) i=(h m).embed (x' m i) := by rw [ht t hl i _ he (le_trans hv (Nat.le_succ _)),ht t hl i _ (le_trans he (Nat.le_succ _)) (Nat.succ_le_succ hv)]; exact embed_comp (C.S.toDepth he p) (h m) _ _
    refine ⟨U.born,hn,fun i _ _ j=>?_,fun i m he _=>?_,fun t hl i j H=> ?_,fun t hl i he=> ?_,fun t ht i he m h hh=> hf t ht i m (le_trans hh (Nat.le_succ _)) he,fun t ht i hd m h hh=>?_,fun i ht hi=> U.native_cross L' N hi ht (fun j=> hf 0 (Nat.zero_le _) j (S.below 0) (Nat.le_succ _) (Q.pinned_init _)),fun m hp i j he hh=> ?_⟩
    · rw [no_steps]; exact (again _ i.le_succ).symm
    · rw [no_steps]; exact upshort (U.begin_age i) (S.mono Q (Q.bounded i) le_rfl) he (Nat.le_succ _)
    · change x' (S.below t).succ i= x' (S.below t).succ j; rw [ht t hl i _ (le_trans (hP t hl) (Nat.le_succ _)) le_rfl,ht t hl j _ (le_trans (hP t hl) (Nat.le_succ _)) le_rfl, zoom_inj C.S _ ((hy t hl i).trans ((Q.lead_eq H _).trans (hy t hl j).symm))]
    · dsimp only; rw [no_steps]; exact hw t hl i _ (hP t hl) le_rfl
    · rw [no_steps]; exact hw (t+1) ht i m (by unfold P priorL; rw [if_neg (by omega),add_tsub_cancel_right]; exact h) hh.le
    exact common_dist L' _ _ hh (by rw [again,again]; exact hx i j he ) -- rw abbrev
-- extra guard in an arrangement
lemma extra_clear (j:I)(he:t<H)(hl:H≤Q.limit)(hv:2*Ω (S.launch t)* (((K (S.launch t)).B^2+2:ℕ):ℝ) < ‖T (L!) (x j)‖): ∀ᶠ p in atTop,∀ m,S.below H ≤ m → (K m).B^2≤ separation (Z p m j) 0:=by
    rw [← sub_zero (T _ (x j)),← grid_zero C.S (L!)] at hv; let l:= S.launch t
    filter_upwards [bubbles _ _ (S.mono Q (he.le.trans hl) le_rfl) _ hv] with p hp m ht; rw [map_zero,behind_zero] at hp
    refine common_dist L' _ _ (i:=l) ((launch_down Q S he hl).le.trans ht) ?_; rw [again,empty_zero]; exact hp -- abbrev
end Canvas
end YM.OPE.Log.Trunk
