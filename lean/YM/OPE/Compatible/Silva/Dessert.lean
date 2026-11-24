import YM.OPE.Compatible.Silva.Cabin
/-! # diversities. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Flume.Script Libra Weir Votive Work.F05
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}{p:Clip}{R:PathData G}
variable (S:StepData c f) (he:Odd S.ratio.count.val)(H:Even c.val)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "Y!"=> AxisChart G X!
local notation "C!"=> Bid.Dir G c
lemma bills_x (k:Kv)(h:S.patch.Branches S.kernel G)(t:S.Choices)(u:C! × Y!)(v:C! × Y!)(hx:ContDiffAt ℝ ω (pane X! t p R) 0): iteratedFDeriv ℝ 2 (pane X! t p R) 0 ![DoubleX S he H k u,DoubleX S he H k v]= iteratedFDeriv ℝ 2 (pane X! t p R) 0 ![u,v]:=by
    have hy:=priceDX S he H (p:=p) (R:=R) h k t; refine Eq.trans ?_ (DFunLike.congr_fun ((hy.iteratedFDeriv ℝ 2).eq_of_nhds) ![u,v]); rw [jets_linear _ (hx.of_le le_top)]; refine congr_arg (iteratedFDeriv ℝ 2 _ 0) (show ![_,_]=(fun i:Fin 2=> DoubleX S he H k (![u,v] i)) from funext fun i=>by fin_cases i<;>rfl) -- parser Fin vector
lemma bills_y (k:Kv)(h:S.patch.Branches S.kernel G)(t:S.Choices)(u:C! × Y!)(v:C! × Y!)(w:C! × Y!)(hx:ContDiffAt ℝ ω (pane X! t p R) 0): iteratedFDeriv ℝ 3 (pane X! t p R) 0 ![DoubleX S he H k u,DoubleX S he H k v,DoubleX S he H k w]= iteratedFDeriv ℝ 3 (pane X! t p R) 0 ![u,v,w]:=by
    have hy:=priceDX S he H (p:=p) (R:=R) h k t; refine Eq.trans ?_ (DFunLike.congr_fun ((hy.iteratedFDeriv ℝ 3).eq_of_nhds) ![u,v,w]); rw [jets_linear _ (hx.of_le le_top)]; refine congr_arg (iteratedFDeriv ℝ 3 _ 0) (show ![_,_,_]=(fun i:Fin 3=> DoubleX S he H k (![u,v,w] i)) from funext fun i=>by fin_cases i<;>rfl)
variable (X:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{B: Bed}{g: Bid.Dir G c→ AxisChart G (forest S.ratio he)} (h:licensed S he X p R L B g) (t:S.Choices)
include X h t
lemma tollY (x y:Y!): iteratedFDeriv ℝ 2 (pane X! t p R) 0 ![(0,x),(0,y)]= dotProduct (cash (countingBasis X! G) x) (FUND S he X*ᵥ cash (countingBasis X! G) y):=by
    let D:= score X! t p R 0; have hs:=viewer t h.2.1; erw [← pack_seat hs.origin,← h.1.metric,← frozen t h.2.1 h.2.2.2,detracts];rfl
private lemma tollZ (u v:C! × Y!)(hp:u.1=v.1)(hx:∀ x:Y!, iteratedFDeriv ℝ 2 (pane X! t p R) 0 ![u,(0,x)]=iteratedFDeriv ℝ 2 (pane X! t p R) 0 ![v,(0,x)]): u=v:=by
    let tK:=countingBasis X! G; have ht:u-v=(0,u.2-v.2):=Prod.ext (by rw [Prod.fst_sub,hp,sub_self]) rfl; let w:=u.2-v.2; let D:=iteratedFDeriv ℝ 2 (pane X! t p R) 0; let A:=cash tK w; have hv:(star A ⬝ᵥ (FUND S he X *ᵥ A))=0:=by
         rw [star_trivial,← tollY S he X h t, show ((0:C!),w)=_ from ht.symm]; let M:=D.curryLeft; change M (u-v) ![u-v]=_; rw [map_sub,ht]; exact sub_eq_zero.mpr (hx w)
    apply sub_eq_zero.mp; rw [ht]; refine Prod.ext rfl ?_; apply tK.equivFun.injective; change A=tK.equivFun 0; rw [map_zero]; exact Classical.byContradiction fun hh => ( (ulk_force S he X).dotProduct_mulVec_pos hh).ne' hv
lemma knowV (k:Kv)(x: Keys G (Limb H)): DoubleX S he H k (fieldT (cabin g) (cloak H x))=fieldT (cabin g) (cloak H x):=by
     let P:=DoubleX S he H k (G:=G); let Q:=fieldT (cabin g) (cloak H x); have ht:=viewer t h.2.1; let W:=twirlF S he H k (G:=G); change P Q=Q; apply tollZ S he X h t
     · change AnalyticNext.QuarticMatch.Joint.shifts _ _ Q.1=Q.1; rw [show Q.1=cloak H x from ht.rim _,spins]
     intro v; rw [ht.hedge]; have he₁:P (0,W v)=(0,v):=Prod.ext (show (AnalyticNext.QuarticMatch.Joint.shifts (G:=G) _ (offset k c) 0)=_ from ((AnalyticNext.QuarticMatch.Joint.shifts (G:=G) (axisK k) (offset k c)).map_zero)) (spinF2 S he H _ _); exact (he₁ ▸ bills_x S _ H k h.1.cover t Q (0,W v) ht.origin).trans (ht.hedge _ _)
lemma knowU (k:Kv)(x y: Keys G (Limb H)): DoubleX S he H k (fieldU (cabin g) (cloak H x) (cloak H y))=fieldU (cabin g) (cloak H x) (cloak H y):=by
     let P:=DoubleX S he H k (G:=G); let Q:=fieldU (cabin g) (cloak H x) (cloak H y); have ht:=viewer t h.2.1; let W:=twirlF S he H k (G:=G); change P Q=Q; apply tollZ S he X h t
     · rw [show Q=(0,Q.2) from ht.lower ..]; exact map_zero (AnalyticNext.QuarticMatch.Joint.shifts (G:=G) (axisK k) (offset k c))
     intro v; apply neg_injective; let V := P (0,W v); have he₁:V=(0,v):= Prod.ext (show (AnalyticNext.QuarticMatch.Joint.shifts (G:=G) _ (offset k c) 0)=_ from ((AnalyticNext.QuarticMatch.Joint.shifts (G:=G) (axisK k) (offset k c)).map_zero)) (spinF2 S he H _ _); nth_rw 1 [←he₁]; change -iteratedFDeriv ℝ 2 _ 0 ![P Q,P (0,W v)]= - _; rw [bills_x S he H k h.1.cover t Q (0,W v) ht.origin,← ht.reserve,←ht.reserve]; exact (bills_y S he H _ h.1.cover t (0,W v) (fieldT _ (cloak H x)) (fieldT _ (cloak H y)) ht.origin).symm.trans (by rw [knowV S _ H X h t k x,knowV S _ H X h t k y,show DoubleX S he H k (0,W v)=_ from he₁] ) -- adjust
end YM.OPE.Cascade.Rill
