import YM.Integration.FVA1Physical.CommonCover.MeasuredReplicaFields

/-! The independent represented model in the replica estimate has the
same numerator and denominator as its original finite Wilson-model push. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.FVA1Physical.OlderPrice
open MeasureTheory Filter RG Wilson Gauge Precision Tree Lattice Exterior
open Comparison.RG02 Order Marker Multi Integral Actual OriginalMixedWilson
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] [Fintype I] {R : Census I}
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}

theorem forest_wilson_reading (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (g β c₀ : ℝ)
    (W : Bulk.Colors R G f) (well : Bulk.Well W) (V : Config G c) :
    let u:=fun y:F.Slice G=>S.density β (F.drape y) V*weight g c₀ (F.drape y) W p P
    let M:=Actual.Push S β (model g c₀ W K) V
    let Y:=fun (s:R.Mode) (y:F.Slice G)=>(Poly.pass (markedLog g (F.drape y) W)).part s
    M.part R.quiet=((∫y,u y ∂F.order G):ℝ) ∧
    Poly.inject (fun s=>FrozenRead.meanOn (F.order G) u (Y s))=unitScale M := by
  intro u M Y
  have rows (s) : M.part s=∫y,u y • Y s y ∂F.order G := by
    change (Actual.Push S β _ V).part s=_
    rw [←forest_read_full F β V K.branches _ (leaf_model K g c₀ W well) (model_gauge K g c₀ W well)]
    rw [forestRead,Set.indicator_univ,components]
    apply integral_congr_ae;filter_upwards [] with y
    change (((S.density β (F.drape y) V:ℂ) • model g c₀ W K (F.drape y)).part s)=_
    simp only [Poly.part_smul,model,Complex.real_smul,u,Y,Complex.ofReal_mul,mul_assoc]
  have one (y) : Y R.quiet y=1 := Poly.pass_part _ (part_lit_quiet _)
  have mass : M.part R.quiet=((∫y,u y ∂F.order G):ℝ) := by
    rw [rows];simp_rw [one,Complex.real_smul,mul_one];exact integral_ofReal
  refine ⟨mass,?_⟩
  funext s
  change (∫y,u y ∂F.order G)⁻¹ • (∫y,u y • Y s y ∂F.order G) = (unitScale M).part s
  rw [unitScale,Poly.part_smul,mass,rows,Complex.real_smul,Complex.ofReal_inv]

end YM.Integration.FVA1Physical.OlderPrice
