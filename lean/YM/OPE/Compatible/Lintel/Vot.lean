import YM.OPE.Compatible.Lintel.Dram
/-!
# Haar two-ring local ink f→I. Includes tax over FREE only. Zero units on trees. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations
open scoped Topology BigOperators Classical ContDiff
variable {I J X Y Z:Type}{G:Gauge}{n m c f:Side} {r d:ℕ} {p q:Clip}{R T:PathData G} {V:ChartRatio G} {σ U D:ℝ}
namespace Script
open Page Virgin
-- use ceremony
variable (S : StepData c f)
def festival (V:ChartRatio G)(R: Bid.Dir G n):ℝ:=∑ i:Edge (Site n), rake V (R (i.1,coord i.2))
lemma festivalS (n:Side)(h:LocalRatio V): ContDiffAt ℝ ω (festival V (n:=n)) 0:=by
     apply ContDiffAt.sum; intro i _; exact (jet_trunk h).1.comp (f:=fun v : Bid.Dir G n => v _) 0 (contDiffAt_apply ..)
lemma fete (P:Tree.Forest S.ratio)(b:AxisChart G P)(h:LocalRatio V): taxY P V b= festival V (arm G f 1 (Stationary.pad P b)):=by
     let p:=arm G f 1 (Stationary.pad P b); let v(i:Edge (Site f)):ℝ:= rake V (edgeColor (Stationary.pad P b) i) -- .fine?
     have he (e: Edge (Site f))(hP:e∈ P.trunks): v e=0:=by unfold v; rw [show edgeColor _ _= 0 from pad_trunk P b ⟨_,hP⟩]; simp [rake,h.anchored]
     symm; change ∑ i, v i=_; rw [← sum_filter_of_ne (p:=fun i=> i∉P.trunks) (fun i _ hh ht=>hh (he i ht))]; erw [sum_subtype (p:=fun i=>i∉P.trunks) _ (fun i=>by simp)];exact sum_congr rfl fun i _=> congr_arg (rake V) (pad_free P b i)
-- shelf 
def dressFee (G:Gauge): Finset (Cover × Shade G):= {0} ×ˢ univ
def polo (G:Gauge) (j:Axis) : shelf (dressFee G) →L[ℝ] G.Color:= LinearMap.toContinuousLinearMap {
   toFun x:= toLp 2 fun i=> x ⟨(0,j,i),by simp [dressFee]⟩
   map_add' _ _:= rfl
   map_smul' _ _:=rfl }
def crownY (V:ChartRatio G): Script (Shade G) 2:= expose (∑ j:Axis,servo (dressFee G) (rake V ∘ polo G j) 2)
lemma crowns (V:ChartRatio G): folk (crownY V):=by
    refine folkS (fun m=>?_) _; choose f h using fun i:Axis=> ser_s (dressFee G) (rake V ∘ polo G i) m 2; exact ⟨_,Sack.finGather (B:=f) _ _ (fun i _=> h i) (fun x=> zero_le_one.trans (payer m _))⟩
lemma crownsS (n:Side)(h:LocalRatio V):Voice (crownY V) (spool G n).toContinuousLinearMap (festival V (n:=n)) :=by
     let L:=(spool G n).toContinuousLinearMap; let P:= dressFee G; let A(t:Site n)(j:Axis):= (rake V ∘ polo G j) ∘ lookS P t; have hv(j:Axis): ContDiffAt ℝ ω (rake V ∘ polo G j) 0:= (show ContDiffAt ℝ ω (rake V) (polo G j 0) from (by rw [map_zero];exact (jet_trunk h).1)).comp 0 (polo G j).contDiff.contDiffAt
     let D(t:Site n)(j:Axis):= A t j ∘ L; have hA(t j): ContDiffAt ℝ ω (A t j) 0:= (show ContDiffAt ℝ ω _ (lookS P t 0) from (lookS P t).map_zero.symm ▸ hv j).comp _ (lookS P t).contDiff.contDiffAt
     have ht(t j): ContDiffAt ℝ ω (D t j) 0:= ((L.map_zero.symm ▸ hA t j : ContDiffAt ℝ ω _ (L 0))).comp _ L.contDiff.contDiffAt
     have hz : festival V (n:=n)=∑ i : Site n,∑ j: Axis,D i j:=by
         funext v; unfold festival; rw [Fintype.sum_prod_type, Finset.sum_apply]; refine sum_congr rfl fun i _=> ?_; rw [Finset.sum_apply]; refine sum_congr rfl fun j _=> ?_; apply congr_arg (rake V); ext k; change v (i,coord j) k= spool G n v (i+wrap n 0,j,k); rw [map_zero,add_zero]; rfl
     have hx (i): ContDiffAt ℝ ω (∑ j:Axis,D i j) 0:=by rw [show ∑ j,D i j=fun z=> ∑ j:Axis,D i j z from funext fun v=> Finset.sum_apply ..]; exact ContDiffAt.sum (fun j _=> ht i j)
     let f(j:Axis):= servo P (rake V ∘ polo G j) 2; intro v; change library n (expose (∑ j,f j)) (L∘v)=_
     rw [expose,libScale,hz,iteratedFDeriv_sum_apply (fun i _=> (hx i).of_le le_top),_root_.sum_apply]; unfold library; rw [mul_sum]; refine Finset.sum_congr rfl fun i _=> ?_; rw [reads_sum _ _ (fun j _=>sootS (ser_s _ (rake V ∘ polo G j) 0 _).choose_spec),mul_sum,iteratedFDeriv_sum_apply (fun j _=> (ht i j).of_le le_top),_root_.sum_apply]; apply sum_congr rfl fun j _=>by rw [show D i j=A i j ∘ L from rfl,jets_linear L ((hA i j).of_le le_top)]; exact (ser_sense _ (rake V ∘ polo G j) 2 (L ∘ v) i ((hv j).of_le le_top)).symm
end Script
end YM.OPE.Flume
