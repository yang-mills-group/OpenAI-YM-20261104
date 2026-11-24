import YM.OPE.Compatible.Atrium.Basil
/-! # Evaluating volume wiring tree kernels. Pre-windows. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations
open scoped Topology BigOperators Classical ContDiff
variable {I J: Type*}{G:Gauge}{n m c f:Side} {r d:ℕ}
namespace Script
open Page
def marry (A:Row I J): Cross 1 I J:= braidRow Prod.snd id A
def shrinkS (n:Side): Ratio n n:=⟨1,mul_one n.val|>.symm⟩
lemma marries (A:Row I J) (n:Side): installed (shrinkS n) (marry A)= A.acts n:=by
    let Q:=shrinkS n; have hz(a:Site n):Q.embed a=a:=by
       rw [← wrap_lift a]; have he(x:Cover):Q.embed (wrap n x)= wrap n x:=by
          rw [Ratio.embed_wrap]; change wrap n ((1:ℕ) • x)= _; rw [one_smul]
       exact he _
    have ha(i : Site n):Q.parent i=i:=by
       nth_rw 1 [← hz i]; exact Q.embed_parent i
    ext i j; unfold installed; erw [Matrix.submatrix_apply, split_co]
    erw [ha]; rfl
lemma payact (A:Row I J)(h:Whole A):Whole (marry A):= braidP Prod.snd id A h
def raft [Fintype J](A: Row I J)(p:Script I r): Script J r:= payVolume (marry A) p -- unused
lemma raftReads [Fintype J](A: Row I J)(h:Whole A)(p:Script I r)(hs:Summable p)(v:Fin r→deck J n):library n (raft A p) v= library n p fun i=>A.acts n *ᵥ v i:=by
    have he:= volume_torque (A:=marry A) (g:=shrinkS n) (payact A h) p hs v; simp_rw [marries] at he;exact he
lemma raftBills [Fintype J](A:Row I J)(h:Whole A)(p:Script I r)(m:ℕ){z:ℝ}(hs:soot m p z):∃ c,soot m (raft A p) c:= volume_bill _ (payact A h) p _ hs
section
variable [Fintype I]
def cityTap (A:Matrix (Tab I n) (Tab I n) ℝ)(p : Script I (r+2))(x: Fin r→deck I n):= ∑ i:Tab I n, ∑ j:Tab I n, A i j*library n p (Fin.cons (deltaH i) (Fin.cons (deltaH j) x))
def boom (p:Script I (r+1))(x: Fin r→deck I n): deck I n:=fun i=>library n p (Fin.cons (deltaH i) x)
lemma dairies (A:Row I I)(h:Whole A)(p:Script I (r+1))(hp:Summable p)(q:Script I (d+1))(hq:Summable q)(x: Fin r→deck I n)(y: Fin d→deck I n): library n (cotton A p q) (Fin.append x y)= dotProduct (boom p x) (A.acts n *ᵥ boom q y):=by
     unfold library; simp_rw [readCotton h hp hq, drawP]; unfold Matrix.mulVec dotProduct; let G (t s:Site n)(i j:Tab I n):= A.acts n i j*scribe t p (Fin.cons (deltaH i) x)*scribe s q (Fin.cons (deltaH j) y)
     have he : (∑ a:Site n,∑ t: Site n,∑ i:Tab I n,∑ j:Tab I n,G a t i j)=∑ i:Tab I n,∑ j:Tab I n,∑ a:Site n,∑ t:Site n, G a t i j:=by
         have hh a : (∑ t:Site n,∑ i:Tab I n,∑ j:Tab I n, G a t i j)= ∑ i:Tab I n,∑ j:Tab I n,∑ t:Site n,G a t i j:= sum_comm.trans (Finset.sum_congr rfl (fun i _=>sum_comm))
         simp_rw [hh];exact sum_comm.trans (Finset.sum_congr rfl (fun i _=>sum_comm))
     rw [show (∑ b:Site n,∑ c:Site n,∑ i:Tab I n,∑ j:Tab I n,_)=_ from he]; apply Finset.sum_congr rfl; intro i _; unfold boom G library; dsimp only; rw [Finset.sum_mul,Finset.sum_comm (s:=univ) (t:=univ) (f:=fun j:Tab I n => fun a:Site n=> ∑ c: Site n, _)]
     apply Finset.sum_congr rfl; intro b _; rw [Finset.mul_sum]; refine sum_congr rfl (fun j _=>?_)
     rw [← Finset.mul_sum]; ring
lemma cellarT (A:Matrix (Tab I n) (Tab I n) ℝ)(p:Script I (r+2))(x: Fin r→deck I n):cityTap A p x=∑ i:Site n,routeTap A p x i:=by
    unfold cityTap library routeTap; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm (s:=univ) (t:=univ) (f:= fun i:Site n=> fun j:Tab I n=> ∑ k: Tab I n,_ )]; apply Finset.sum_congr rfl; exact fun i _=> sum_comm
end
end Script
end YM.OPE.Flume
