import YM.Integration.WilsonSeparatedOriginalSlabCenterPhase

/-! The shared signed centre is a period-independent bounded functional on the actual four-dimensional cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabCenterBill
open Function Finset Set MeasureTheory RG Lattice Wilson Source RG05Readout RG05Readout.Native
open WilsonSeparatedOriginalSlabCenterPhase
open scoped BigOperators Classical Topology
variable {I:Type}[Fintype I]

def read (v:I→Axis→ℝ)(f:C(Axis→ℝ,ℂ)):ℂ:=
  ∫ z in Native.box, f (fun d=>z d) * center v z

private theorem entered (v:I→Axis→ℝ)(f:C(Axis→ℝ,ℂ)):
    IntegrableOn (fun z:E4=>f (fun d=>z d)*center v z) Native.box:=by
  apply ContinuousOn.integrableOn_compact Pert.Cellular.cells_compact
  have chart' : Continuous (fun z:E4=>(fun d:Axis=>z d)):=by fun_prop
  exact ((f.continuous.comp chart').mul (regular _)).continuousOn

def invoice (v:I→Axis→ℝ):C(Axis→ℝ,ℂ)→ₗ[ℂ]ℂ where
  toFun:=read v
  map_add' f g:=by
    unfold read
    simp only [ContinuousMap.coe_add,Pi.add_apply,add_mul]
    exact integral_add (entered v f) (entered v g)
  map_smul' c f:=by
    unfold read
    simp only [ContinuousMap.coe_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc]
    exact integral_const_mul ..

theorem paid (v:I→Axis→ℝ)(f:C(Axis→ℝ,ℂ)){B:ℝ}
    (budget:∀x∈Metric.closedBall (0:Axis→ℝ) (1/2),‖f x‖≤B):
    ‖invoice v f‖≤volume.real Native.box * B:=by
  change ‖∫z in Native.box,f (fun d=>z d)*center v z‖≤_
  rw [mul_comm]
  apply norm_setIntegral_le_of_norm_le_const Pert.Cellular.cells_compact.measure_lt_top
  intro z hz
  rw [norm_mul,show ‖center v z‖=1 from unit _ _,mul_one]
  exact budget _ (chart z hz)

theorem normalized (v:I→Axis→ℝ)(f:C(Axis→ℝ,ℂ)):
    ‖invoice v f‖≤∫z in Native.box, ‖f (fun d=>z d)‖:=by
  apply (norm_integral_le_integral_norm _).trans_eq
  simp only [norm_mul,show ∀z:E4,‖center v z‖=1 from fun _=>unit _ _,mul_one]

end YM.Integration.WilsonSeparatedOriginalSlabCenterBill
