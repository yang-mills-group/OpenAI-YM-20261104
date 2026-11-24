import YM.Integration.WilsonIndependentSpoutHaar

/-! The inversion Jacobian on the actual free directions of its forest.
All pinned tree links have their true zero Jacobian income. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutHaarTree
open Set Filter Lattice RG WilsonCoeffUV RegulatorIR RegulatorIR.Geometry RegulatorIR.Geometry.Field
open RegulatorIR.Prim RegulatorIR.Binding RegulatorIR.Laplace PertExtension PertExtension.Orb
open Tree Tree.Forest WilsonIndependentSpoutWilsonAction
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)

theorem seats (y:Meadow G (Wind F)) :
    (∑ i:OEdge f,entry G (injectX F y i)) = ∑ i:Wind F,entry G (y i) := by
  let a:=Equiv.sumCompl (Field.branch F)
  rw [←a.sum_comp (fun i=>entry G (injectX F y i)),Fintype.sum_sum_type]
  change (∑ k:Knot F,entry G (injectX F y k.val))+(∑ k:Wind F,entry G (injectX F y k.val))=_
  simp_rw [inject_others,ent_zero,inject_access,Finset.sum_const_zero,zero_add]

theorem genuine (hf:Even f.val)(y:Meadow G (Wind F)):
    (fun t:ℝ=>unhaar (XSpace.Bare.chart G) (opening (t • injectX F y))) =ᶠ[𝓝 0]
      fun t=>2*psyche (Wind F) G y t := by
  have ht:Tendsto (fun t:ℝ=>t • injectX F y) (𝓝 0) (𝓝 0):=by
    have h:Continuous (fun t:ℝ=>t • injectX F y):=continuous_id.smul continuous_const
    simpa only [zero_smul] using h.tendsto 0
  filter_upwards [ht.eventually (WilsonIndependentSpoutHaar.folded hf)] with t H
  rw [H,←map_smul (injectX F),seats];rfl

theorem signed (hf:Even f.val)(y:Meadow G (Wind F)):
    tale (fun t:ℝ=>unhaar (XSpace.Bare.chart G) (opening (t • injectX F y))) =
      PowerSeries.C 2 * tale (psyche (Wind F) G y) := by
  have H:=psyche_smooth (Wind F) G y
  rw [tale_eq (contDiffAt_const.mul H) (genuine F hf y)]
  change tale ((fun _:ℝ=>(2:ℝ))*psyche (Wind F) G y)=_
  rw [tale_mul contDiffAt_const H,Script.dictates contDiffAt_const (Script.oneC 2)]

end YM.Integration.WilsonIndependentSpoutHaarTree
