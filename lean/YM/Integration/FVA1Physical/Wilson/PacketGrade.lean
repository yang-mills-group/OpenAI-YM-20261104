import YM.Integration.FVA1Physical.Wilson.RecastColors

/-! Every reconstructed physical clock-field source has its stated actual
engineering order as a full symmetric tensor, including off-diagonal field
and clock directions needed at the inherited next step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Lattice RG Marker Multi Exterior Tree Precision
open Comparison.RG02 Assembly Valence Adjacent
open scoped Classical Topology ContDiff BigOperators
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem clockForm_grade {f:X→ℂ} (hf:ContDiffAt ℝ ω f 0) (k:ℕ):GradeAt k (clockForm k f):=by
  have sm:ContDiffAt ℝ ω (clockForm k f) 0:=(clockForm_analytic hf k).contDiffAt
  refine ⟨sm,fun j hj=>?_⟩
  apply Tensor.ext_diag _ _ (Analysis.sym_Jet (sm.of_le le_top)) (fun _ _=>rfl)
  funext x
  change _=(0:ℂ)
  apply (smul_right_inj (show (j.factorial:ℝ)⁻¹≠0 from by positivity)).mp
  change jet (clockForm k f) j x=_
  rw [clockForm_jet hf k j x,if_neg (ne_of_lt hj),smul_zero]

theorem clockPacket_grade {e r:ℕ} {U:ℕ→X→ℂ} (degree:∀j≤r,Level ((e+j:ℕ):ℤ) (U j)):
    GradeAt e (clockPacket e r U) := by
  unfold clockPacket
  exact GradeAt.list_sum (range (r+1)) (fun j=>clockForm (e+j) (U j)) fun j hj=>
    (clockForm_grade (degree j (mem_range_succ_iff.mp hj)).smooth.contDiffAt (e+j)).lower (Nat.le_add_right ..)

variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] {R:Census I}
  {c f:Side} {S:StepData c f} {p:Clip} {P:PathData G} {O:ChartRatio G}
  (K:Bulk.Kernel S p P O) (F:Forest S.ratio) (tag:S.Choices) (C:Bulk.Colors R G f) (η:I→ℕ)
  (r:ℕ) (cost:UnitCost) (base:Bulk.Colors R G c)

theorem recast_grade (valid:∀a:Hot R,C.power a=QuadraticLocal.Sunrise.Launch.index R η a.val+1) (s:Hot R):
    let bank:=recastColors K F tag C η r cost base
    GradeAt (bank.power s) (Bulk.projected (bank.mark s)) := by
  intro bank
  exact (clockPacket_grade (fun j hj=>loopReset_degree K F tag C η s r cost valid j hj)).depends
    (germPainter_chart K F tag C η s r cost).symm

end YM.Integration.FVA1Physical.Wilson
