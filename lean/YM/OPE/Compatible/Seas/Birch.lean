import YM.OPE.Compatible.Seas.Lease
/-!
# Angular trigon, buys orthogonality
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle.Pose
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Extra.FD.OPE
open Next.Rank.Radian (dV stroll)
variable (p q: Pose) {F:E4→ℝ}{s:ℝ}
def ThetaS (P Q:Axis→E4→ℝ)(a b:Axis):=P a*Q b-P b*Q a
def OmegaS (P:Pose)(a b:Axis):= P.pureD [b] a-P.pureD [a] b
def TauS (P:Axis→E4→ℝ)(a b:Axis):= grad b (P a)-grad a (P b)
abbrev half_sum (P:Axis→Axis→ℝ):=∑ a:PlaqAxes,P a.val.1 a.val.2
private lemma half_eq (f:Axis→Axis→ℝ):half_sum f=∑ a:Axis,∑ b:Axis,if a<b then f a b else 0:=by -- reindex
    rw [half_sum, show ∑ a:PlaqAxes,f a.val.1 a.val.2=(∑ a∈ Finset.univ.filter (fun a:Axis×Axis=> a.1<a.2),f a.1 a.2) from ?_,Finset.sum_filter,Fintype.sum_prod_type]
    exact (Finset.sum_subtype (p:=fun a:Axis×Axis=> a.1<a.2) (s:=Finset.univ.filter (fun a=> a.1<a.2)) (fun x=>by simp) (fun i:Axis×Axis=>f i.1 i.2)).symm
lemma angle (f:Axis→Axis→ℝ)(hf:∀ a,f a a=0)(hs:∀ a b,f a b=f b a)(he:∑ a:Axis, ∑ b:Axis,f a b=0): half_sum f=0:=by
    let g(a b:Axis):=if a<b then f a b else 0; have hh(a b:Axis): f a b=g a b+g b a:=by
       unfold g; rcases lt_trichotomy a b with h|h|h; · simp [h, not_lt_of_ge h.le]
       · subst b; simp [hf]
       · simp [h, not_lt_of_ge h.le]; exact hs _ _
    simp_rw [hh,Finset.sum_add_distrib] at he; rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun a b=>g b a)] at he; rw [half_eq]; change ∑ a:Axis, ∑ b:Axis,g a b=0; linarith only [he]
private lemma fealty {V W:Axis→E4→ℝ} {Q:Axis→Axis→ E4→ℝ}(he:∀ a b,Q b a=-Q a b)(hs:0<s)(hg:∀ i,epic (V i))(hh:∀ i,epic (W i))(hk:∀ i j,epic (Q i j))(hv:∑ a:Axis,∑ b:Axis,fineI s (V a*W b*Q a b)=0):half_sum (fun a b=>fineI s (ThetaS V W a b*Q a b))=0:=by
    let y(a b):= fineI s (V a*W b*Q a b); have h(a b):fineI s (ThetaS V W a b*Q a b)= y a b + y b a:=by
       rw [ThetaS,sub_mul,iSub hs (epic_m (epic_m (hg a) (hh b)) (hk a b)) (epic_m (epic_m (hg b) (hh a)) (hk a b))]; unfold y
       rw [he a b,mul_neg,← neg_one_smul ℝ (V b*W a*Q a b),iSc]; ring
    apply angle; · intro a; simp [ThetaS,fineI]
    · intro a b; rw [h a b, h b a, add_comm]
    simp_rw [h,Finset.sum_add_distrib]; rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun a b=>y b a), show (∑ a:Axis,∑ b:Axis,y a b)=_ from hv,zero_add]
-- Csm.W curl. swapped R.
lemma balsamic (hs:0<s){V:Axis→E4→ℝ}(hp:∀ a,Spherical (V a) (p.aLen []+q.aLen []+1)):half_sum (fun a b=>fineI s (ThetaS (p.pureD []) (q.pureD []) a b *TauS V a b))=0:=by
   have hv(a b:Axis): epic (grad a (V b)):=fun _ _=> grad_smooth_at (hp b).size.smooth.contDiffAt a
   apply fealty (fun a b=>neg_sub ..|>.symm) hs (p.hint []) (q.hint []) (fun i j=> epic_s (hv j i) (hv i j))
   let P(a):= p.pureD [] a; let Q:=q.pureD []
   change ∑ a:Axis,∑ b:Axis,fineI s (P a*Q b*(grad b (V a)-grad a (V b)))=0
   have he(a b c e:Axis): epic (P a*Q b*grad c (V e)):=epic_m (epic_m (p.hint [] a) (q.hint [] b)) (hv c e)
   have h(a: Axis): ∑ b:Axis,fineI s (P a*Q b*grad b (V a))=0:=by simp_rw [mul_comm (P a)]; exact q.slouch p hs _ ((add_comm (p.aLen []) _ ▸ hp a))
   simp_rw [mul_sub,fun a b=>iSub hs (he a b b a) (he a b a b),Finset.sum_sub_distrib]; rw [Finset.sum_comm (f:=fun a b=>fineI s (P a*Q b*grad a (V b)))]; simp_rw [h, fun b=> show (∑ i:Axis,fineI s (P i*Q b*grad i (V b)))=0 from p.slouch q hs _ (hp b), Finset.sum_const_zero,sub_self]
-- Csing omega
lemma cerate (hs:0<s){V:Axis→E4→ℝ}(hp:∀ a,Spherical (V a) (p.aLen [0]+q.aLen []))(hv:∑ i,grad i (V i)=0): half_sum (fun a b=>fineI s (ThetaS (q.pureD []) V a b*OmegaS p a b))=0:=by
   have h(a):epic (V a):= fun x _=> (hp a).size.smooth.contDiffAt
   apply fealty (fun a b=> (neg_sub ..).symm) hs (q.hint []) h (fun i j=> epic_s (p.hint [j] i) (p.hint [i] j))
   let P(a b:Axis):=p.pureD [a] b; let Q:= q.pureD []; have he(a b:Axis): fineI s (Q a*V b* OmegaS p a b)=fineI s (P b a*Q a*V b)-fineI s (P a b*Q a*V b):=by rw [show Q a*V b*OmegaS p a b=P b a*Q a*V b-P a b*Q a*V b from by change _*_*(_-_)=_;ring]; exact iSub hs (epic_m (epic_m (p.hint _ _) (q.hint _ _)) (h _)) (epic_m (epic_m (p.hint _ _) (q.hint _ _)) (h _))
   change ∑ a:Axis,∑ b:Axis,fineI s (Q a*V b*OmegaS p a b)=0
   simp_rw [he,Finset.sum_sub_distrib]; rw [Finset.sum_comm (f:=fun a b=>fineI s (P a b*Q a*V b))]; unfold P Q; simp_rw [fun i=> bary p q hs hp hv i i,fun i=>p.stint q hs i (hp i),Finset.sum_const_zero,sub_self]
end YM.OPE.Nestle.Pose
