import YM.Contact.Nested
import YM.Contact.GridBundle

/-! Coarse price of an ordinary collection of distinct microscopic slots in one cell,
with no cancellations required. The bound is simultaneous on all widths, through the same
base-order follower as the signed grid receipts. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace YM.Contacts.Nested
open Function Filter Set Lattice Wilson RG Cells Extraction Push Push.RelayDifference MeasureTheory
open scoped BigOperators Topology Classical
open YM.MergeProof.Ribbons
variable {G:Gauge}{C:Family G}{p N J m j k l:ℕ}{I:Type*}[Fintype I](f:Extraction.Order)
variable {Q:Schedule}
lemma note_shifted (q:ℕ)(hg:Q.Gentle): Note Q (fun j:ℕ=>Q.a (j+q)) (-1):=by
    classical induction q with
    | zero=> exact Note.note_a Q
    | succ q ih=> simp_rw [show ∀ j:ℕ,j+(q+1)=j+1+q from fun _=>by omega] at *; exact ih.scales hg

lemma many_steps (q:ℕ): ∀ j:ℕ, Q.a (j+q) ≤ Q.a j /2^q:=by
    intro j; induction q with
    | zero=> simp
    | succ q ih=>
       have H:= Q.a_step (j+q); rw [← add_assoc]; rw [H,pow_succ,← div_div]
       exact div_le_div₀ (div_nonneg (Q.a_pos j|>.le) (by positivity)) ih (by norm_num) (by exact_mod_cast (le_trans (by decide) (Q.block_large _) : 2 ≤ (Q.block _).val))

lemma cast_cutoff (hm:m≤J)(hk:J≤k)(hf:k≤N)
       {x:I→ Site (C.side N p)}(hp:∀ i i',‖C.S.place (x i)‖+ ‖C.S.place (x i')‖ + C.S.a J < C.S.a m)
       (hy:∀ i j:I,i≠j → 2*C.S.a J < ‖C.S.place (x i - x j)‖)
       (hb:(Fintype.card (Signed × I):ℝ)*10*C.S.a k < C.S.a J):
       (∀ i i',pdist (x i)+pdist (x i') + Cells.span C.S (hk.trans hf) p < Cells.span C.S (hm.trans (hk.trans hf)) p) ∧
       (∀ i j:I,i≠j→Cells.span C.S (hk.trans hf) p < separation (x i) (x j)) ∧
       Fintype.card (Signed × I)*(2*(3*Cells.span C.S hf p+Cells.span C.S hf p+1)) < Cells.span C.S (hk.trans hf) p:=by
     have hs (i:Site (C.side N p)):= normC C N p i
     have hN{v:ℕ}(hv:v≤N) : C.S.a N * (Cells.span C.S hv p:ℝ)=C.S.a v:= C.S.embeds_scale _
     have h0:0<C.S.a N:=C.S.a_pos N
     refine ⟨fun i i'=>?_,fun i i' hne=>?_,?_⟩
     · have hQ i : C.S.a N * (pdist (x i):ℝ) ≤ ‖C.S.place (x i)‖ := by simpa only [separation,sub_zero] using (hs (x i)).1
       rw [←hN (hk.trans hf),← hN (hm.trans (hk.trans hf))] at hp
       have This : C.S.a N * ((pdist (x i)+pdist (x i')+Cells.span C.S (hk.trans hf) p:ℕ):ℝ)< C.S.a N * (Cells.span C.S (hm.trans (hk.trans hf)) p:ℝ):=by push_cast; nlinarith only [hp i i',hQ i, hQ i']
       exact_mod_cast lt_of_mul_lt_mul_left This h0.le
     · specialize hy i i' hne
       rw [←hN (hk.trans hf)] at hy
       have hz := (hs (x i-x i')).2; rw [separation,sub_zero] at hz
       have This : C.S.a N * (Cells.span C.S (hk.trans hf) p:ℝ)< C.S.a N * ((pdist (x i-x i')):ℝ) := by linarith only [hy,hz]
       exact_mod_cast lt_of_mul_lt_mul_left This h0.le
     have hir:= (C.S.toDepth hf p).count.property
     apply lt_of_le_of_lt (Nat.mul_le_mul_left (Fintype.card (Signed × I)) (show 2*(3*Cells.span C.S hf p+Cells.span C.S hf p+1)≤10*span C.S hf p by
       have hj:0<span C.S hf p:=hir; omega))
     rw [←hN hf, ←hN (hk.trans hf)] at hb
     have hcast : C.S.a N * ((Fintype.card (Signed × I)*(10*Cells.span C.S hf p):ℕ):ℝ) < C.S.a N * (Cells.span C.S (hk.trans hf) p:ℝ):=by push_cast; nlinarith only [hb]
     exact_mod_cast lt_of_mul_lt_mul_left hcast h0.le

def locAt (O:I→C.book.Token)(x:I→Site (C.side N p))(V:Config G (C.side N p)):ℂ:=∏ i,C.O N p (O i).2 (x i) V
      -- `V` is actual cutoff connection.
lemma cluster_fund (f:Extraction.Order)(h:C.Makes)(O:I→C.book.Token)(hm:m≤J)(hk:J≤k)(t:I → Cover)
       (hp:∀ i i':I,‖C.S.gridPoint l (t i)‖+‖C.S.gridPoint l (t i')‖+ C.S.a J < C.S.a m)
       (hr:∀ i,8*‖C.S.gridPoint l (t i)‖≤ C.S.a m)
       (hy:∀ i j:I,i≠j → 2*C.S.a J < ‖C.S.gridPoint l (t i-t j)‖)
       (hb:(Fintype.card (Signed × I):ℝ)*10*C.S.a k < C.S.a J)
       (A:I→ℝ) (hf:∀ i,∀ᶠ u:ℕ×ℕ in f.fuse,BlockCost (Q:=C.S) (N:=u.1) (p:=u.2) (C.O u.1 u.2 (O i).2 0) k (C.beta u.1 u.2) (A i)) :
       ∀ᶠ u:ℕ×ℕ in f.fuse, BlockCost (Q:=C.S) (N:=u.1) (p:=u.2) (fun v=>∏ i:I,C.O u.1 u.2 (O i|>.2) (Cells.location C.S l u.1 u.2 (t i)) v) m (C.beta u.1 u.2) (∏ i:I,A i) :=by
     let x (u:ℕ×ℕ) i :=Cells.location C.S l u.1 u.2 (t i)
     have hz : ∀ᶠ u:ℕ×ℕ in f.fuse,k≤u.1 ∧l≤u.1:=by rw [Order.fused,Order.late]; filter_upwards with v; filter_upwards [f.mesh.cofinal.eventually (eventually_ge_atTop k),f.mesh.cofinal.eventually (eventually_ge_atTop l)] with w he ha; exact ⟨he,ha⟩
     have hrs (i:I): ∀ᶠ u:ℕ×ℕ in f.fuse,∀ hm:m≤u.1,∀ a: Site (C.side u.1 u.2),8*‖C.S.place a‖≤ C.S.a m →∀ v:C.label (O i).1,Interior ((center C.S u.2 hm 0).chamber 0) (C.O u.1 u.2 v a):=by
        rw [Order.fused,Order.late]; filter_upwards with v; filter_upwards [f.mesh.cofinal.eventually (near_center C m (O i).1 h)] with w hw hm a ht v;exact hw hm _ a ht v
     have hgrid(t:I → Cover) := (eventually_all.mpr fun i:I=>fused_grid (C:=C) (l:=l) f (t i))
     filter_upwards [hz,eventually_all.mpr hf, hgrid t,eventually_all.mpr (fun i=>hgrid (t-fun _=>t i)),eventually_all.mpr hrs] with u hkN he hc hq ht
     let n:=u.1; let p:=u.2
     have hmN:m≤n := hm.trans (hk.trans hkN.1)
     let Y(i:I):= C.O n p (O i).2 (0:Site (C.side n p))
     have ht': (fun v=> ∏ i:I,C.O u.1 u.2 (O i).2 (x u i) v) = clusterAt (x u) Y :=funext fun y=>Finset.prod_congr rfl fun i _=>by
              unfold RelayDifference.oriented; simp only [pull_one]; change C.O n p _ _ _=Y i _
              simpa only [zero_add,Y] using (C.translation (0:Site _) (x u i) (O i).2 y).symm
     have hi(i): 8* ‖C.S.place (x u i)‖ ≤ C.S.a m :=by rw [hc i]; exact hr i
     have hps(i j) : ‖C.S.place (x u i)‖ + ‖C.S.place (x u j)‖+C.S.a J < C.S.a m := by dsimp only [x]; rw [hc,hc]; exact hp i j
     have hcst (i j)(hi:i≠ j): 2*C.S.a J < ‖C.S.place (x u i-x u j)‖ := by
       dsimp only [x]; specialize hq j i; rw [Cells.location,dif_pos hkN.2] at hq
       rw [Cells.location,dif_pos hkN.2,Cells.location,dif_pos hkN.2]
       change C.S.place ((C.S.toDepth hkN.2 _).embed (wrap _ (t i-t j)))= _ at hq
       rw [map_sub,← Ratio.root_embed, map_sub, Ratio.root_embed, Ratio.root_embed] at hq -- THESE rewrites
       exact hq.symm ▸ hy i j hi
     obtain ⟨hsize,hsep,hLim⟩:=cast_cutoff hm hk hkN.1 hps hcst hb
     refine ⟨hmN,?_,?_⟩
     · let B(i:I)(v:Config G (C.side n p)):=C.O n p (O i).2 (x u i) v
       have hvalid (i): Interior ((center C.S p hmN 0).chamber 0) (B i):=ht i hmN _ (hi i) _
       have hv (s:Finset I): Interior ((center C.S p hmN 0).chamber 0) (∏ i ∈ s,B i) := by
            classical induction s using Finset.induction with
            | empty => rw [Finset.prod_empty]; exact (show Interior ((center C.S p hmN 0).chamber 0) (fun _:Config G (C.side n p)=> (1:ℂ)) from Interior.constant _ _)
            | insert i s hi ih => rw [Finset.prod_insert hi]; exact (hvalid i).times ih
       convert hv Finset.univ using 1
       ext v; rw [Finset.prod_apply]
     suffices hz': (center C.S p hmN 0).rootTest (C.beta u.1 u.2) (clusterAt (x u) Y) ≤ ∏ i:I,A i by exact ht'.symm ▸ hz'
     exact (coarser_product hm hk hkN.1 h (x u) Y A hsize hsep hLim he)

lemma rough_cluster (f:Extraction.Order)(hh:C.Makes)(hv:CellHyp C f)(R:ℕ→ℝ)(hR:Note C.S R (-1))
       (tail:ℕ→ℝ)(hTail:Tendsto tail atTop (𝓝 0))(a:ℝ)(ha:0<a)(hGrid:∀ j:ℕ,C.S.a (j+2) ≤ R j /128)
       (O:I→C.book.Token) (m:ℕ): ∀ᶠ j:ℕ in atTop, ∀ (l:ℕ) (t:I → Cover), (∀ i,‖C.S.gridPoint l (t i)‖ ≤ a*tail j) →
       (∀ i i':I,i≠i' → R j/a ≤ ‖C.S.gridPoint l (t i-t i')‖) →
       ∀ᶠ u:ℕ×ℕ in f.fuse, BlockCost (Q:=C.S) (N:=u.1) (p:=u.2) (fun v=>∏ i:I,C.O u.1 u.2 (O i).2 (Cells.location C.S l u.1 u.2 (t i)) v) m (C.beta u.1 u.2)
         (∏ i:I,(R j)^(-(O i|>.fst:ℝ)-2)):=by
     let L(i:ℕ):= (C.S.block i).val
     let E(i:I)(j:ℕ):=(R j)^(-(O i|>.fst:ℝ)-2)
     obtain ⟨q,hq⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2:ℝ))).eventually_gt_atTop ((Fintype.card (Signed × I):ℝ)*10)).exists
     obtain ⟨q',hq'⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2:ℝ))).eventually_gt_atTop (2*a)).exists
     let J(j:ℕ):ℕ:=j+2+q'; let k(j:ℕ):ℕ:=j+(2+q')+q
     let v(i:I):= (O i).2
     choose M hM AM hPos hAM using fun i=> hv.centered (O i).1 1 (1+‖v i‖) one_pos (by linarith [norm_nonneg (v i)])
     have hfee(i:I):∀ᶠ j:ℕ in atTop,∀ᶠ u:ℕ×ℕ in f.fuse,
          BlockCost (Q:=C.S) (N:=u.1) (p:=u.2) (C.O u.1 u.2 (O i).2 0) (k j) (C.beta u.1 u.2) (E i j) :=by
       have hw := note_shifted (Q:= C.S) ((2+q')+q) C.path.levels.fits.mesh; let R':ℝ:=-(O i|>.fst:ℝ)-1
       have hv': Note C.S (fun j=> (AM i+1)*(C.S.a (k j))^(R')) (-R'):=by simpa only [k,add_assoc,mul_neg,mul_one,zero_add] using (Note.notes C.S _ (show 0<AM i+1 by linarith only [hPos i])|>.mills (hw.powr R'))
       have hE': Note C.S (E i) (-R'+1):=(hR.powr _|>.swapP (by unfold R';ring))
       filter_upwards [eventually_ge_atTop (M i), hv'.outweigh hE' (by linarith)] with j hj hFee
       have h := hAM i (k j) (hj.trans (by dsimp [k];omega)) (C.S.a (k j)^R') (Real.rpow_pos_of_pos (C.S.a_pos _) _)
       rw [Order.fused]; refine h.mono fun p hx=>hx.mono fun n hn=> ?_
       obtain ⟨hp,hP⟩:=hn
       obtain ⟨hx,hr⟩:= hP (v i) (by change ‖v i‖≤_; linarith) 0
       change (center C.S _ hp 0).rootTest _ _ ≤ AM i * C.S.a (k j) ^ R' + C.S.a (k j)^R' at hr
       rw [show AM i * C.S.a (k j)^R' + C.S.a (k j)^R'= (AM i+1)*C.S.a (k j)^R' by ring] at hr
       exact ⟨hp,hx,hr.trans hFee⟩
     have hd:= ((note_shifted (Q:=C.S) (2+q') C.path.levels.fits.mesh).thins (by norm_num : (-1:ℝ)<0)).eventually (gt_mem_nhds (by positivity [C.S.a_pos m] : (0:ℝ)<C.S.a m/2))
     have hT:= hTail.eventually (gt_mem_nhds (by positivity [C.S.a_pos m] : (0:ℝ)<C.S.a m/(16*a)))
     filter_upwards [eventually_ge_atTop m,eventually_all.mpr hfee,hd,hT] with j hj hF hJ hT l t hdist hgap
     change C.S.a (j + (2 + q')) < C.S.a m/2 at hJ
     change tail j < C.S.a m/(16*a) at hT
     have hp: C.S.a (J j) < C.S.a m/2:=by simpa only [J,Nat.add_assoc] using hJ
     have ht': a*tail j < C.S.a m/16:=by have := (lt_div_iff₀ (show 0<16*a by positivity)).mp hT; linarith
     have hs : 2*C.S.a (J j) < R j/a := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (many_steps q' (j+2)) zero_le_two) (by
       apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hGrid j) (by positivity)) zero_le_two); have hrp j := hR.pos j
       field_simp; nlinarith only [mul_lt_mul_of_pos_left hq' (hrp j),show 0<(2:ℝ)^q'*R j from mul_pos (by positivity) (hrp _)])
     have hCount : (Fintype.card (Signed × I):ℝ)*10*C.S.a (k j) < C.S.a (J j) := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (show C.S.a (k j)≤ _ from by exact (Nat.add_assoc j 2 q').symm ▸ many_steps q (j+2+q')) (by positivity : (0:ℝ) ≤ (Fintype.card (Signed × I):ℝ)*10)) (by
       apply lt_of_lt_of_le (mul_lt_mul_of_pos_right hq (div_pos (C.S.a_pos _) (by positivity))) (?_); show _ ≤ C.S.a (j+2+q'); rw [Nat.add_assoc]; field_simp; exact le_rfl)
     exact cluster_fund f hh O (show m≤J j by unfold J; omega) (show J j≤ k j by unfold J k; omega) t (fun i i'=>by linarith only [hp,ht',hdist i, hdist i',(C.S.a_pos m).le]) (fun i=>by linarith only [ht',hdist i,(C.S.a_pos m).le]) (fun i i' hi'=>hs.trans_le (hgap i i' hi')) hCount (E · j) hF
end YM.Contacts.Nested
