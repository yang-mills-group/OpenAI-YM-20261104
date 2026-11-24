import YM.Integration.WilsonPositionProgramFiledGaussianChange

/-! The true occupied and quiet generators on one shifted Wilson fluctuation before its Wick integration. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramRecastDraw
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Order Comparison.RG02.Assembly
open WilsonPositionProgramFiledGaussianChange
open scoped BigOperators Classical

variable {G:Gauge}{c f:Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(tag:S.Choices)
  {V:Type}[DecidableEq V][Fintype V]{R:Census V}

theorem occupied (W Y:Bulk.Colors R G f)(A:fieldDir G c 1){r:ℕ}(i:Hot (Board R r))
    (hit:(Join.left i.val).val.Nonempty)(z:Precision.Key F G→ℝ):
    let d:=(Join.right i.val).val.card
    let s:Hot R:=⟨Join.left i.val,hit⟩
    let b:=(Bulk.translated K F A z).2
    Cloud.paint z (drivers K F tag W A r i-drivers K F tag Y A r i) =
      (d.factorial:ℂ)*(Assembly.jet (Bulk.markFn S F W s) (W.power s+d) (1,b)-
        Assembly.jet (Bulk.markFn S F Y s) (Y.power s+d) (1,b)) := by
  dsimp only
  have t:Assembly.translate (Bulk.stage K F A) (Bulk.hinge F) z=(1,(Bulk.translated K F A z).2):=by
    change Bulk.translated K F A z=_
    rw [Bulk.footing]
  simp only [drivers,Assembly.generator,dif_pos hit,map_sub,map_smul,Assembly.reading,t,smul_eq_mul,mul_sub]

theorem quiet (W Y:Bulk.Colors R G f)(same:W.vac=Y.vac)(A:fieldDir G c 1){r:ℕ}
    (i:Hot (Board R r))(off:¬(Join.left i.val).val.Nonempty):
    drivers K F tag W A r i-drivers K F tag Y A r i=0 := by
  have eqn:Bulk.geometric K F tag W=Bulk.geometric K F tag Y:=by
    funext x
    simp only [Bulk.geometric,Bulk.fee,Bulk.supplement,Bulk.posed,same]
  simp only [drivers,Assembly.generator,dif_neg off,eqn,sub_self]

end YM.Integration.WilsonPositionProgramRecastDraw
end
