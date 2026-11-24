import YM.OPE.Compatible.Seas.Pup
/-!
# Angular calculator, Toe
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle.Pose
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Extra.FD.OPE
open Next.Rank.Radian (dV)
variable (p q: Pose)
variable {U:Gloam}{F G:E4→ℝ}{s:ℝ}
abbrev epic (F:E4→ℝ):=∀ x∈away, ContDiffAt ℝ ∞ F x
lemma hint (l:List Axis)(i:Axis): epic (p.pureD l i):=by
   unfold pureD Lck; refine fun x hx=> ContDiffAt.sub ?_ ?_ -- wrong
   · split; apply Next.Rank.Radian.stroll _ (freeSmooth hx); exact contDiffAt_const
   split; apply Next.Rank.Radian.stroll _ (freeSmooth hx); exact contDiffAt_const
lemma iSumA (hs:0<s)(hf:epic F)(hg:epic G): fineI s (F+G)=fineI s F+fineI s G:=by
   unfold fineI; simp_rw [Pi.add_apply,mul_add]; exact integral_add (μ:=volume) (f:=annA s*F) (g:=annA s*G) ((iceAway _ hf).continuous.integrable_of_hasCompactSupport (HasCompactSupport.mul_right (shipA hs))) ((iceAway _ hg).continuous.integrable_of_hasCompactSupport (HasCompactSupport.mul_right (shipA hs))) -- defeq.
lemma iSub (hs:0<s)(hf:epic F)(hg:epic G): fineI s (F-G)=fineI s F-fineI s G:=by
   unfold fineI; simp_rw [Pi.sub_apply,mul_sub]; exact integral_sub (μ:=volume) (f:=annA s*F) (g:=annA s*G) (show Integrable (annA s*F) from (iceAway _ hf).continuous.integrable_of_hasCompactSupport (HasCompactSupport.mul_right (shipA hs))) (show Integrable (annA s*G) from (iceAway _ hg).continuous.integrable_of_hasCompactSupport (HasCompactSupport.mul_right (shipA hs)))
lemma iSumK {E:Type*}(A:Finset E)(f:E→E4→ℝ)(hs:0<s)(H:∀ i∈A,epic (f i)):fineI s (∑ i∈A, f i)=∑ i∈A, fineI s (f i):=by
   induction A using Finset.induction_on with
   | empty=> simp [fineI]
   | insert i A hi ih=>
      have he:=H i (Finset.mem_insert_self ..); have ht(j)(hj:j∈A):=H j (Finset.mem_insert_of_mem hj); rw [Finset.sum_insert hi,Finset.sum_insert hi,iSumA hs he (fun x hx=>?_),ih ht]; rw [funext fun x=>(Finset.sum_apply x A f)]; exact ContDiffAt.sum (fun j hj=> ht j hj x hx)
lemma iSc (s a:ℝ): fineI s (a • F)=a*fineI s F:=by unfold fineI; rw [← integral_const_mul]; congr 1; ext i; simp only [Pi.smul_apply,smul_eq_mul];ring
abbrev epic_m (hf:epic F)(hg:epic G):epic (F*G):=fun x hx=> (hf x hx).mul (hg _ hx)
abbrev epic_s (hf:epic F)(hg:epic G):epic (F-G):=fun x hx=>(hf x hx).sub (hg _ hx)
def path (p:Pose)(l:List Axis)(a:Axis):List Axis:=l++a::p.m -- duplicate binder
abbrev aLen (p:Pose)(l:List Axis):= l.length+1+p.m.length
lemma path_len (p:Pose)(l a):(p.path l a).length=p.aLen l:=by simp [path,aLen];omega
-- finite notation
private def serviceI (s:ℝ)(l p:List Axis):= countM s 0 1/brim (l.length+p.length)*mash (l.length+p.length)*nut l.length*nut p.length
def Spoor (s:ℝ)(j k:ℕ):=countM s 0 1/brim (j+k)*mash (j+k)*nut j*nut k
theorem toQ (hs:0<s)(l m:List Axis)(a b:Axis)(h:Spherical F (p.aLen l+q.aLen m)): fineI s (p.pureD l a*q.pureD m b*F)=
    Spoor s (p.aLen l) (q.aLen m)* p.Lck (fun i=> q.Lck (fun j=> dV (p.path l i++q.path m j) F 0) b) a:=by
   let c:= Spoor s (p.aLen l) (q.aLen m)
   let A (i):=tint (p.path l i); let B(i):=tint (q.path m i)
   have ha(i j): epic (A i * B j * F):=fun x hx=> ((Next.Rank.Radian.stroll _ (freeSmooth hx)).mul (Next.Rank.Radian.stroll _ (freeSmooth hx))).mul h.size.smooth.contDiffAt
   let K(i j):= dV (p.path l i++q.path m j) F 0; have hw(i j):fineI s (A i*B j*F)=c*K i j:=by rw [show _= _ from fine_duo (l:=p.path l i) (p:=q.path m j) hs (show Spherical F _ by rw [path_len,path_len]; exact h)]; simp only [path_len]; unfold c Spoor K;ring
   change fineI s (p.Lck A a * q.Lck B b*F)= _;
   have H3 : epic (q.Lck B b):= q.hint m _
   have hv(i): fineI s (A i * q.Lck B b*F)= c*q.Lck (K i) b:=by
      apply Hlock (T:=q) b (f:=fun Y=> fineI s (A i * Y * F)) B (u:=c) (K i) (hw i) (by simp[fineI]) (fun i=> NextAway _) ?_
      intro x y hx hy; simp_rw [mul_sub,sub_mul]; exact iSub hs (epic_m (epic_m (NextAway _) hx) (fun x _=>h.size.smooth.contDiffAt)) (epic_m (epic_m (NextAway _) hy) (fun x _=>h.size.smooth.contDiffAt))
   apply Hlock (T:=p) a (f:=fun Y=>fineI s (Y*q.Lck B b*F)) A (u:=c) (fun i=>q.Lck (K i) b) hv (by simp[fineI]) (fun _=> NextAway _) ?_
   intro x y hx hy; simp_rw [sub_mul]; exact iSub hs (epic_m (epic_m hx H3) (fun x _=>h.size.smooth.contDiffAt)) (epic_m (epic_m hy H3) (fun x _=>h.size.smooth.contDiffAt))
where
 NextAway (l:List Axis):epic (tint l):=fun x hx=>Next.Rank.Radian.stroll l (freeSmooth hx)
 Hlock {T:Pose}(a:Axis){u:ℝ}(f:(E4→ℝ)→ℝ)(B:Axis→E4→ℝ)(g:Axis→ℝ)(hg:∀ i,f (B i)=u*g i)(hh:f 0=0)(hb:∀ i,epic (B i))(h:∀ x y: E4→ℝ, epic x → epic y → f (x-y)=f x-f y): f (T.Lck B a)=u*T.Lck g a:=by
    unfold Lck; rw [h,mul_sub]; rotate_left
    · split; exact hb _; exact fun _ _=>contDiffAt_const
    · split; exact hb _; exact fun _ _=>contDiffAt_const
    split_ifs <;> simp only [hg,hh,mul_zero]
end YM.OPE.Nestle.Pose
