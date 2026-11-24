import YM.OPE.Compatible.Plains.Whip
/-!
# Leading finite Wick polynomial. transport H⊆...
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell FreeResolvent Paver Rill Saga Shrew
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{U:Gloam}{d k j r w e m:ℕ}{I:Type}[Fintype I] {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
omit [Fintype I] -- linter may error
lemma bare_entry (x y:Site N)(p q:Reed G)(h:4 ≤ r): ProbeCov (Cot L G (Train.top r) N) (fence p x) (fence q y) =if p.2=q.2 then tip q.1 (fun i=>paper p.1 i x) y else 0:=by
   let f:= fence p x; let g:= fence q y; let M:=Cot L G (Train.top r) N
   have he: ProbeCov M f g=g (fun a=> f (fun b=>M b a)):=by
       rw [axisCash]; unfold ProbeCov; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [axisCash f (fun b=>M b i), Finset.sum_mul]
   rw [show ProbeCov _ _ _= _ from he,show g _= _ from fee q y _]; let T(a:Axis)(v: Site N):= f (fun b=>M b (v,a,q.2))
   have hv(i:Axis)(k:Site N): T i k= if p.2=q.2 then paper p.1 i x k else 0:=by
       let F(t:Axis)(w:Site N):= M (w,t,p.2) (k,i,q.2); rw [show T i k=tip p.1 F x from fee ..]; split
       next hp=> rw [show F= _ from ?_]; apply tipPapers
                 funext t v; change (if p.2=q.2 then lineC (ShellRow L (Train.top r)) N (v,Exterior.coord t) (k,Exterior.coord i) else 0)=(if t=i then mildX _ _ else _); rw [if_pos hp]; simp only [strip_field (C:=L) h,coord_iff] -- values
       next hp=> rw [show F=0 from funext fun i=>funext fun v => if_neg hp]; exact tip_zero ..
   change tip q.1 T y=_; rw [show T=_ from funext fun i=>funext fun k=>hv i k]; split_ifs <;> first | rfl | exact tip_zero ..
def firm (p q:Reed G): ℝ:= if p.2=q.2 then zine q.1 p.1.icicle else 0
lemma falls {F:Filter I}(p:Nestle.Pose){x:I→Axis→Cover→ℝ}{b:Axis→Cover→ℝ}(hp:∀ i v,Tendsto (fun l=>x l i v) F (𝓝 (b i v))): Tendsto (fun i=>zine p (x i)) F (𝓝 (zine p b)):=by
    have he(v): Tendsto (fun i=>(stern p.a (x i p.b)-stern p.b (x i p.a)) v) F (𝓝 ((stern p.a (b p.b)-stern p.b (b p.a)) v)):=by apply Filter.Tendsto.sub ( (hp p.b _).sub (hp p.b v)) ((hp p.a _).sub (hp p.a v))
    have ht(l:List Axis)(v:Cover):Tendsto (fun i=>rain l (stern p.a (x i p.b)-stern p.b (x i p.a)) v) F (𝓝 (rain l (stern p.a (b p.b)-stern p.b (b p.a)) v)):=by induction l generalizing v with | nil=>exact he _| cons i l ih=>exact Filter.Tendsto.sub (ih _) (ih _)
    exact ht _ _
lemma barometer (p q:Reed G)(f:ℕ→Side)(z:(i:ℕ)→Site (f i))(hp:Tendsto (fun i=>(f i).val) atTop atTop)(hv:∀ᶠ i in atTop,Even (f i).val)(h:4 ≤ r): Tendsto (fun i=>evenCov r L (f i) (z i) p q) atTop (𝓝 (firm p q)):=by
    unfold evenCov; simp_rw [bare_entry (L:=L) _ _ p q h]; unfold firm; split_ifs
    next he=>
       simp_rw [zine_tent]; apply falls; intro i a; unfold paper; simp_rw [sub_sub_cancel,← map_add]; unfold Pose.icicle Pose.ray Pose.Lck; split_ifs <;> first | exact Filter.Tendsto.sub (calm f hv hp (a+p.1.x) _) (calm f hv hp (a+p.1.x) _) | exact Filter.Tendsto.sub (calm f hv hp (a+p.1.x) _) (tendsto_const_nhds (x:= (0:ℝ))) | exact Filter.Tendsto.sub (tendsto_const_nhds (x:= (0:ℝ))) (calm f hv hp (a+p.1.x) _) | exact tendsto_const_nhds
    next he=> exact tendsto_const_nhds
end YM.OPE.Prairies
