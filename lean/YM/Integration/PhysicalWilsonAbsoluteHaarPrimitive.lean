import YM.Integration.PhysicalWilsonFreeLinkHaar
import YM.Comparison.RG02.Bulk.Fk

/-! Absolute Haar density and stored nonlinear fields on the original forest slice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalWilsonAbsoluteHaarPrimitive
open Function Lattice Wilson RG Precision Exterior Tree FreeResolvent WilsonCoeffUV
open RGComparison.Core16.Descent Comparison.RG02 Marker Multi
open scoped Classical BigOperators Topology
variable {G:Gauge} {c f:Side} (S:StepData c f) (F:Forest S.ratio) (O:ChartRatio G)

def chart (a:AxisChart G F):TreeVars G f:=flatten (sliceCoord S F a)

theorem edge (a:AxisChart G F) (e:Edge (Site f)):
    dij O (dyes (chart S F a) e)=O.J (if h:e∈F.trunks then 0 else a ⟨e,h⟩):=by
  unfold dij dyes
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change O.J (collect G (Bid.stretch F (0,a)) e)=_
  rw [Work.F01.collect_vertical]

theorem absolute (hO:LocalRatio O) (a:AxisChart G F):
    unhaar O (chart S F a)=∑i:F.Free,Real.log (O.J (a i)):=by
  classical
  unfold unhaar
  rw [←Fintype.sum_subtype_add_sum_subtype (fun e:Edge (Site f)=>e∈F.trunks)
    (fun e=>Real.log (dij O (dyes (chart S F a) e)))]
  have erased: (∑e ∈ @Finset.univ {e:Edge (Site f)//e∈F.trunks}
      (Subtype.fintype (fun e=>e∈F.trunks)),Real.log (dij O (dyes (chart S F a) e.1)))=0:=by
    apply Finset.sum_eq_zero
    intro e _
    rw [edge S F O,dif_pos e.2,hO.anchored,Real.log_one]
  refine (congrArg₂ (· + ·) erased ?_).trans (zero_add _)
  apply Finset.sum_congr rfl
  intro i _
  rw [edge S F O,dif_neg i.2]

theorem jacobian (hO:LocalRatio O) (a:AxisChart G F) (ha:∀i,a i∈Metric.ball 0 O.radius):
    Real.log (∏i:F.Free,O.J (a i))=unhaar O (chart S F a):=by
  rw [absolute S F O hO,Real.log_prod (fun i _=>(hO.pos _ (ha i)).ne')]

theorem material (a:AxisChart G F):
    F.drape (fun i=>G.lieExp (a i))=mantle (chart S F a):=by
  rw [drape_coord S F,chart,placed]

variable {V:Type} [DecidableEq V] [Fintype V] {H:Census V}
  (W:Bulk.Colors H G f) (p:Clip) (P:PathData G)

omit [Fintype V] in
theorem action (hO:LocalRatio O) (g:ℝ) (B:fieldDir G c 1) (a:AxisChart G F)
    (ha:∀i,a i∈Metric.ball 0 O.radius):
    let U:=F.drape (fun i=>G.lieExp (a i))
    let X:=chart S F a
    mainTerm p P U+noiseTaylor S (represent B) U (tac S)+
      g^2*(loop P U-Real.log (∏i:F.Free,O.J (a i)))+W.vac g U=
      mainTerm p P (mantle X)+jointPen G S (Sum.elim X (flatten B))+
        g^2*(loop P (mantle X)-unhaar O X)+W.vac g (mantle X):=by
  dsimp only
  rw [PhysicalWilsonFreeLinkHaar.coordinates S F B a,jacobian S F O hO a ha,material S F a]
  rfl

omit [Fintype V] in
theorem marked (g:ℝ) (s:Hot H) (a:AxisChart G F):
    W.mark s g (F.drape (fun i=>G.lieExp (a i)))=W.mark s g (mantle (chart S F a)):=by
  rw [material S F a]

end YM.Integration.PhysicalWilsonAbsoluteHaarPrimitive
end
