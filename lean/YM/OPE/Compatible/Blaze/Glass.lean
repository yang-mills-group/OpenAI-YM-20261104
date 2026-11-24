import YM.OPE.Compatible.Blaze.Swan
/-! # Page reflection. CL on solar -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix Tree
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Stationary
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Pilot Woody Virgin Work.F08 Flume.Page
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
open YM.AnalyticNext.QuarticMatch.Joint
variable {n c f:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type} (a:Axis)
local notation "T"=> Shade G
local notation "W"=> Tab T n
def plusa (x:Page T r):Page T r:=fun i=> ((Wm a).act (x i).1+dust a (x i).2.1,(x i).2)
lemma twinS (x:Page T r): plusa a (plusa a x)=x:=funext fun _=>Prod.ext (offsets a _ _) rfl
def spark (x:Page T r):ℝ:=∏ i,if (x i).2.1=a then -1 else 1
lemma spark_tw (x:Page T r):spark a x*spark a x=1:=by unfold spark; rw [← Finset.prod_mul_distrib,Finset.prod_eq_one]; intro i _; split<;>ring
lemma sparkR (x:Page T r): ‖spark a x‖=1:=by
    let v:=spark a x; have h:v*v=1:= spark_tw a x; have hv : ‖v‖* ‖v‖=1:=by rw [←norm_mul,h,norm_one]
    change ‖v‖=1; nlinarith [norm_nonneg v]
lemma sparkC (x:Page T r): spark a (plusa a x)=spark a x:=rfl
def shapeR (r:ℕ)(p:Script T r): Script T r:=fun x=>spark a x*p (plusa a x)
lemma discoS (p:Script T r):shapeR a r (shapeR a r p)=p:=funext fun i=>by simp only [shapeR,sparkC,twinS, ←mul_assoc,spark_tw,one_mul]
lemma fog_m (i:Axis):dust a i (R:=Per n)=wrap n (dust a i):=by unfold dust; split_ifs <;> simp
lemma sigIce (p:Bid.Dir G n)(i:Axis)(j:G.ColorIndex)(v:Cover)(x:Site n): spool G n (streak a G n p) (x+wrap n v,i,j)= (if i=a then -1 else 1)*spool G n p ((Wm a).act x+wrap n ((Wm a).act v+dust a i),i,j):=by
     change (streak a _ _ p (x+wrap _ v,Exterior.coord i)) j= _*p _ _; simp_rw [α_line,map_add, Signed.act_add, wrap_signed,fog_m]; rw [add_assoc]; split_ifs<;> simp
lemma replicate (p:Page T r)(i:Fin r→Bid.Dir G n)(x:Site n): render x p (fun j=>spool G n (streak a G n (i j)))= spark a p*render ((Wm a).act x) (plusa a p) (spool G n ∘ i):=by unfold spark render; rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun j _=> sigIce ..
lemma rightS (p:Script T r)(x: Site n)(i:Fin r→Bid.Dir G n): scribe x (shapeR a r p) (spool G n ∘ i)= scribe ((Wm a).act x) p (fun j=>spool G n (streak a G n (i j))):=by
    let E:Equiv.Perm (Page T r):=⟨plusa a,plusa a,twinS a,twinS a⟩; unfold scribe; rw [← Equiv.tsum_eq E (fun q=> p q*render _ q _)]; apply tsum_congr; intro k; rw [replicate,show E k=plusa a k from rfl,twinS,← Signed.act_mul,ζFlags,Signed.act_one]; unfold shapeR; rw [sparkC]; ring
lemma sortedS (p:Script T r) (h:p.sorted): (shapeR a r p).sorted:=by
    intro i; ext1 u; change spark a (u∘i) * _= _; rw [show spark a (u∘i)=spark a u from Equiv.prod_comp i (fun j=> if (u j).2.1=a then (-1:ℝ) else 1)]; exact congr_arg (fun x=>spark a u *x) (congr_fun (h i) (plusa a u))
lemma replicate_fee (x:Page T r): figure m (plusa a x) ≤ (r+1:ℝ)^m*figure m x:=by
    have hf(i: Axis): size (dust a i) ≤ 1:=by unfold dust;split<;>simp [size,Lattice.step_apply, eq_comm, apply_ite Int.natAbs]
    have hh(b:Cover):size ((Wm a).act b)=size b:=by unfold size; simp_rw [run_axis]; exact Finset.sum_congr rfl fun i _=>by split<;>simp
    let V:=plusa a x; have hv(j:Fin r):size (V j).1≤ size (x j).1+1:=(size_add ..).trans (add_le_add (hh _).le (hf _))
    have hZ: Flume.Page.stamp V≤ Flume.Page.stamp x+r:=by simp_rw [Page.perimeter]; refine le_trans ?_ ?_ (b:=1+∑ i:Fin r,(size (x i).1+1)); exact Nat.add_le_add_left (Finset.sum_le_sum (fun i _=>hv i)) _; rw [Finset.sum_add_distrib]; simp [add_assoc]
    have hg: Flume.Page.stamp V≤ (r+1)* Flume.Page.stamp x:=by
        have hz:1 ≤ Flume.Page.stamp x:=by rw [Page.perimeter]; omega
        nlinarith
    change (Flume.Page.stamp V:ℝ) ^ m ≤ _* (Flume.Page.stamp x:ℝ)^m; rw [←mul_pow]; exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hg) _
lemma lifePrice (p: Script T r)(K:ℝ)(v:soot m p K): soot m (shapeR a r p) ((r+1:ℝ)^m*K):=by
    let E:Equiv.Perm (Page T r):=⟨plusa a,plusa a,twinS a,twinS a⟩; let q:= shapeR a r p; let f(i):=figure m (E i)*‖q (E i)‖; let C':ℝ:=(r+1:ℝ)^m; have hf(i:Page T r): f i=figure m (E i)*‖p i‖:=by unfold f q shapeR; congr 1; rw [show plusa a (E i)=i from twinS ..,norm_mul,sparkR,one_mul]
    let g(i):=figure m i*‖q i‖; have he: SumBudget f (C'*K):=by
          let z(i):= C'*(figure m i* ‖p i‖); have ht:0 ≤ C':= by unfold C'; positivity
          have hp:SumBudget z (C'*K):=⟨fun i=> mul_nonneg ht (v.1 _), v.2.1.mul_left _,(tsum_mul_left (a:=C')).trans_le (mul_le_mul_of_nonneg_left v.2.2 ht)⟩; apply budget_minor hp; · intro i; rw [hf]; exact mul_nonneg (figure_pos _).le (norm_nonneg _)
          intro i; rw [hf]; exact (mul_le_mul_of_nonneg_right (replicate_fee a i) (norm_nonneg _)).trans_eq (mul_assoc ..)
    exact ⟨E.surjective.forall.mpr he.1,E.summable_iff.mp he.2.1,(E.tsum_eq g).symm.trans_le he.2.2⟩
end YM.OPE.Quit
