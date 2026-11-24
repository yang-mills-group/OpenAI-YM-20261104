import YM.OPE.Compatible.Estuary.Tights
/-!
# Charge inserted as **first slot**. goes from scalar shelf sensor to row. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I:Type}[Fintype I] {G:Gauge}{n m c:Side}{r k:ℕ}
namespace Script
open Page
omit [Fintype I] in
def tack (i:I)(p:Script I r):Script I (r+1):= Sack.rope (Fin.cons ((0:Cover),i)) p
omit [Fintype I] in
lemma tack_bill (i:I){p:Script I r}{C:ℝ}(h:soot k p C): soot k (tack i p) C:=by
   let f:Page I r→Page I (r+1):= fun q:Page I r=> Fin.cons ((0:Cover),i) q
   have he(q:Page I r): figure k (f q)=figure k q:=by
       have ht:stamp (f q)=stamp q:=by simp [Page.perimeter,Fin.sum_univ_succ,f,size]
       change (stamp _:ℝ)^k=_; rw [ht]; rfl
   exact (Sack.cart f h zero_le_one (payer k) (fun i=>by rw [he,mul_one])).tips (by simp)
set_option maxHeartbeats 200000 in
lemma tackAt (i:I){p:Script I r}(h:Summable p)(x:Fin r→deck I n)(y:deck I n) (z:Site n): scribe z (tack i p) (Fin.cons y x) = y (z,i) * scribe z p x:=by
   let f:Page I r→Page I (r+1):= fun q:Page I r=> Fin.cons ((0:Cover),i) q; have he(q:Page I r): render z (f q) (Fin.cons y x)=y (z,i)*render z q x:=by unfold render; rw [Fin.prod_univ_succ]; simp [f]
   unfold scribe; let g :Page I r→ℝ:= fun q=>p q* render z (f q) (Fin.cons y x); have ht :g=(fun q=>y (z,i)*(p q*render z q x)):= funext fun q=>by unfold g; rw [he];ring
   have hs:Summable (fun q=> y (z,i)*(p q*render z q x)):=((instruments p h z x).summable.mul_left _); have hp: Summable g:=ht.symm ▸ hs; unfold tack; rw [Sack.cart_bill f (fun i=> render z i (Fin.cons y x)) hp]
   change (∑' i,g i)=_; rw [ht,tsum_mul_left]
lemma tackBoom (i:I){p:Script I r}(h:Summable p)(x:Fin r→deck I n)(z: Site n)(j:I): boom (tack i p) x (z,j)= if i=j then scribe z p x else 0:=by
   unfold boom library; simp_rw [tackAt i h x]; unfold deltaH; by_cases he:i=j
   · subst j; rw [if_pos rfl, Finset.sum_eq_single z]; simp; exact fun j _ h=> by simp [h]
     simp -- hj unused
   rw [if_neg he]; apply sum_eq_zero fun p _=> ?_; rw [Pi.single_apply]; simp [he]
-- families pencil at all n
section tools
variable (S: Finset (Cover×I))(X:I→ shelf S→ℝ)
def vitalX (x:deck I n):deck I n:=fun i=>X i.2 (lookS S i.1 x)
def ledgeB (r:ℕ):Script I (r+1):= ∑ i:I,tack i (expose (servo S (X i) r))
lemma ledgeBudget (r:ℕ):folk (ledgeB S X r):=by
   intro k; choose c h using fun i=> ser_s S (X i) k r; exact ⟨_,Sack.finGather (B:=fun i=> _*c i) _ _ (fun i _=>tack_bill _ (Sack.scale_line (h i) _)) (fun i=> zero_le_one.trans (payer k _))⟩
lemma ledgeDiff (h:∀ i, ContDiffAt ℝ ω (X i) 0) (n:Side): ContDiffAt ℝ ω (vitalX S X (n:=n)) 0:=contDiffAt_pi.mpr fun i=> ((show ContDiffAt ℝ ω _ (lookS S i.1 0) from (lookS S i.1).map_zero.symm ▸ h i.2)).comp _ (lookS S i.1).contDiff.contDiffAt
lemma ledgeFilm (h:∀ i, ContDiffAt ℝ ω (X i) 0) (v:Fin r→deck I n): iteratedFDeriv ℝ r (vitalX S X (n:=n)) 0 v=boom (ledgeB S X r) v:=by
    funext i; let V(j:I):= expose (servo S (X j) r); let k:I→ Script I (r+1):= fun j=>tack j (V j); have hp(j):= (Sack.scale_line (ser_s S (X j) 0 r|>.choose_spec) (r.factorial:ℝ)); have hv: boom (ledgeB S X r) v i=∑ j:I, boom (k j) v i:= by unfold boom library; change (∑ i':Site n, scribe i' (∑ j,k j) _)=_; simp_rw [reads_sum univ k (fun i _=>sootS (tack_bill i (hp i)))]; exact sum_comm
    rw [hv]; simp_rw [show ∀ j:I,boom (k j) v i=_ from fun j=> tackBoom j (p:=V j) (sootS (hp j)) v i.1 i.2, Finset.sum_ite_eq', mem_univ,if_true,show scribe i.1 (V i.2) v= _ from score_scaled i.1 _ v (r.factorial:ℝ)]
    let L: deck I n →L[ℝ]ℝ:=ContinuousLinearMap.proj i; exact ((show iteratedFDeriv ℝ r (vitalX S X (n:=n)) 0 v i= iteratedFDeriv ℝ r (L ∘ vitalX S X) 0 v from (DFunLike.congr_fun (L.iteratedFDeriv_comp_left (ledgeDiff S X h n) le_top) v).symm)).trans (ser_sense S (X i.2) r v i.1 ((h _).of_le le_top))
end tools
end Script
end YM.OPE.Flume
