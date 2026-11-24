import YM.OPE.Compatible.Glades.Numeric
/-!
# Complete coordinated grid reduction

Does not apply at arbitrary collision limits. Finite cutoff inputs full
selected sectors; next use at continuum *fixed configurations* and finally
move to general placements using later interpolation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.CutOrder
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float Next.Rank Station Next.Rank.Spindle
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset Cells Ribbon
open scoped Topology Classical
variable {X:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X)
open YM.OPE.Allot Series Lights
variable {G:Gauge} {C:Family G} {A:Allot C} {J k b n d N p:ℕ}{l:ℕ→ℕ}
set_option quotPrecheck false
variable {m σ j:X→ℕ}{Q:Finset X}{o:X→Track C.path (Site (C.side J p)) p} {z w:ℝ}
-- entrance
local notation "Z!"=>listP C p J
local notation "E"=> Mix.camp C p J
local notation "X'"=> brim D Q
variable (Y:brim D Q→ℕ)
variable (v:∀ i:brim D Q,C.label (Y i))(u:brim D Q→ ℝ)
variable (h : CutOrder C (listP C p J) D Q m j N p (Mix.camp C p J) o b l)(hz : Expenses C D Q m j l b z)
local notation "V'"=> Site (C.side J p)
def grove (C:Family G)(Q:Finset X)(m:X→ℕ)(σ:X→ℕ)(z:ℝ)(u:brim D Q →ℝ):ℝ:= z^(Q.card*(places X+places X))*∏ i:brim D Q, Run.Below C.path (u i) (σ i.val+1) (finishAt D m i.val)
local notation "M"=> grove D C Q m σ z u
omit [OrderBot X] [PartialOrder X] [Fintype X] in
private lemma changeHead (A:Allot C) (_ : RG.History G){V:Type} [Fintype V] [DecidableEq V] {P : Ensemble V}{x:Finset X}{X₁ Y₁ Y₂: Track C.path V p}{m₁ m₂ : ℕ}{z z':ℝ} {U:V→ Config G (C.S.side N p)→ℂ}{h h'}
    (H : Head x A P m₁ N p b X₁ Y₁ U z h) (he:Y₁=Y₂)(hz:z=z')(hu:m₁=m₂): Head x A P m₂ N p b X₁ Y₂ U z' h':=by subst Y₁ m₂ z'; exact H

include h hz
set_option maxHeartbeats 200000 in
lemma fullyJoined (A:Allot C) (hA:C.Makes)(hG:G.Simple)(hx:Stock.Tabs.opens C.path.levels 1 J k)(ho:k ≤ n)(hp:n+1=m ⊥)(hN:n<N)(hK:C.ref d ≤ k)
    (hW:∀ i,m ⊥ ≤ i→ places X ≤ A.r i)(hr:GridApprox.room C.path.levels J n (lensScope C d))(hE:o ⊥=Mix.camp C p J)(hb: 1 ≤ b)
    (hu:∀ i:X',0<u i)(hs:∀ i:X', C.ref (Y i) ≤ σ i.val ∧ σ i.val < N ∧ finishAt D m i.val ≤ σ i.val+1 ∧ Migrating C.path (σ i.val+1) p N (o i.val)∧ 2*u i*Next.Rank.Spindle.paid C (Y i) (σ i.val+1) N p (v i)≤ fly C.path.levels (Y i) (σ i.val+1))
    (g: Config G (C.side N p)→ℂ)
    (h_f:g=fun W=> ∏ i:brim D Q, C.O N p (v i) (o i.val N 0) W)(hg:Interior ((center C.S p (hx.1.trans (ho.trans hN.le)) 0).chamber 0) g)
    (hC:∀ t:C.label d,Interior ((center C.S p (hx.1.trans (ho.trans hN.le)) 0).chamber 0) (C.O N p t 0)) :
    ∃ z':C.label d, Next.UVStress.quota C d n N p z' ≤ 2*(owed C M d n) ∧ Interior ((center C.S p (hx.1.trans (ho.trans hN.le)) 0).chamber 0) (g-C.O N p z' 0)∧ (center C.S p (hx.1.trans (ho.trans hN.le)) 0).rootTest (C.beta N p) (g-C.O N p z' 0) ≤ 2*(stakes C J k/rebate C M d k n):=by
   let r:ℕ:= m ⊥; let W:= center C.S p (hx.1.trans (ho.trans hN.le)) 0; let t(i:X):= finishAt D m i; let H:=C.path
   let f (i:brim D Q):= C.O N p (v i) (o i.val N 0); let ξ:= listP C p J; let F (i:V'×X'):= W.copy i.1 (f i.2); let S:= h.plan
   have hI(i:X'): roof Q m N i.val=N:=if_neg ((on_brim ..).mp i.2|>.1)
   have ht(i:X'): i.val∈allUp D Q:= mem_union_right _ i.2
   have hy(i:X'): r ≤ t i.val:=lower_earliest D Q m S _ (ht _)
   have hw(i:X'):∃ L':Line A Z! N p (t i.val) N b E (o i.val), L'.w (t i.val)=Run.Below H (u i) (σ i.val+1) (t i.val)∧ Budges Z! H N p (far C.path.levels N) (L'.w N) (E N) (L'.X N) (fun j=>F (j,i)):=by
       obtain ⟨hn,hv,hsX,hY,hL⟩:= hs i
       have hm:t i.val ≤ N:= hsX.trans hv
       have hθ: finishAt D m i.val ≤σ i.val+1:=hsX
       obtain ⟨L',hL,hb,hL'⟩:= fresh_line A Z! (v i) hA hb (h.head.le.trans (hy i)) hn hθ hv ⟨fun j hi hj=>h.moves.mare j ((hy i).trans hi) hj⟩ hY (fun j hi hj=>h.pare _ (ht i) j hi (hj.trans_le (le_trans hv ((hI i).symm.le)))) (fun j hk hn=> h.echo _ (ht i) j (hθ.trans hk) (hn.trans ((hI i).symm.le))) (hu _) hL
       have hP: (fun x: V'=>fun y=>stepUp (ξ.move x) (o i.val N x) (C.O N p (v i) 0) y) = fun j=>F (j,i) :=by
          funext j; unfold F; change stepUp (ξ.move j) (o i.val N j) (C.O N p (v i) 0)=_; rw [show W.copy j (f i) = stepUp (ξ.move j) ((Mix.camp C p J) N j) (f i) from (handmove C _ _ _ _ _ _).symm]
          rw [show f i= _ from (itemT C N p _ hA (v i) (o i.val N 0)).symm, flyF]
          by_cases he:j=0; · subst j; rw [zeroMama C J p N (hx.1.trans (ho.trans hN.le)), show ξ.move 0=(1,false) from P_on ..]; simp only [affine,Signed.act_one,add_zero]
          rw [← show (o i.val N j)= affine (ξ.move j).1 (Mix.camp C p J N j) (o i.val N 0) from h.echo _ (ht i) N hm ((hI i).symm.le) j he]
       exact ⟨L',hL,hP ▸ hb⟩
   choose L HL hl using hw
   let X0:Lights A ξ N p (fun i:X'=>finishAt D m i.val) N b (Mix.camp C p J) (fun i=>o i.val):=L
   let Y₀:= birth (Names V' X') (C.path.rep N p N) F
   have hK':Occupancy (tags X0.tips) (A.r N):= X0.rim ▸ h.count_left D A S (Subset.refl _) (fun i hx=> (hI ⟨i,hx⟩).symm.le) h.next.le (hW N (hp ▸ hN)) -- cast notation
   have hp': Integrable Y₀ (prior G _):= (hatCont C N p _ (fun i:V'×X'=> cappedC C J p N _ (fun _=>f i.2) (i.1,false) (C.continuousO ..)) (show Continuous ((H.rep N p N).eval) by rw [(hA.wilson.starts ..).2]; exact bare_cont _) _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   have hX0:X0.LitUp (full (Site (C.side J p)) X') (gust H N p N Y₀ N le_rfl):=by rw [gust_base]; refine ⟨hp',Y₀,hp',fun _ _ _=> rfl,?_⟩; exact Stem.flushed (X:=X0.tips) (W:=X0.asks) (g:=fun i v=>F (v,i)) hl hA.wilson A.buy.system.costs.night hK'
   have hU:= windfall D A h S (Subset.refl _) F (fun i hx=> (hI ⟨i,hx⟩).symm.le) le_rfl h.next hp' X0 hz hG hA hW hX0
   let a₁:=grove D C Q m σ z u
   have hs: ∀ j:V', W.copy j g = parcel (C:=C) F j :=by
      intro j; rw [h_f]; funext y; unfold Tiling.copy F parcel; change _=∏ i:X', W.copy j (f i) y; unfold Tiling.copy; split_ifs <;> simp only [star_prod] <;> rfl
   have hh:Head ({⊥}:Finset X) A Z! (n+1) N p b E E (fun i:V'=> W.copy i g) a₁ hN:=by
      -- use heq transport
      have hf:0<z:=hz.good
      rw [funext hs]; refine show _ from ?_
      have heq': (z^(Q.card*(places X+places X))*∏ i,X0.bottom i) = a₁:= by unfold a₁ grove; congr 1; exact prod_congr rfl fun i _=> HL i
      have hT:r ≤ N:= hp.symm.trans_le (show n+1≤ N from hN)
      exact changeHead A H hU hE heq' hp.symm -- edit
   have h0:0<a₁:=mul_pos (pow_pos hz.good _) (prod_pos fun i _=> Run.below_fee _ (hu _))
   refine draw A hN hx ho g hK (Nat.le_of_lt_succ (lt_of_lt_of_le h.head hp.symm.le)) hG hA hr h0 ?_ hC hg hh -- adjust
   rw [h_f]; exact continuous_finsetProd _ fun x _=> C.continuousO ..
end YM.OPE.Arboreal.CutOrder
