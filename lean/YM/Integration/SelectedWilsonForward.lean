import YM.Integration.PositiveWilsonMarkedInput
import YM.Integration.ActualSelectedModelIntegral
import YM.Integration.WilsonJointMoment

/-! Apply a complete signed polynomial readout to the *same* selected
original Wilson push and its prescribed model, on every coarse field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedWilsonForward
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {C : Family G} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
local notation "W₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "W₁" => C.path.rep datum.cutoff datum.period (datum.level+1)
local notation "op₀" => C.path.levels.clock.op datum.level datum.period
local notation "b₀" => C.path.β datum.cutoff datum.period (datum.level+1)
local notation "nc" => C.side datum.level datum.period
local notation "nf" => C.side (datum.level+1) datum.period

/-- An arbitrary fixed complex linear combination of all physical modes. -/
def read (c : B.Mode → ℂ) : Poly B →L[ℂ] ℂ := ∑ s, c s • Poly.get s

omit [Fintype V] in
theorem value (c : B.Mode → ℂ) (y : Poly B) : read c y = ∑ s,c s*y.part s := by
  simp only [read,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  rfl

omit [Fintype V] in
private theorem chosen_slice {f d : Side} (S : StepData d f) {β : ℝ} (h : S.IsKernel β G)
    (L : Poly B →L[ℂ] ℂ) {g : Config G f → Poly B} (hg : Integrable g (prior G f)) (U : Config G d) :
    L (S.push β g U) = S.push β (fun T => L (g T)) U := by
  let P := L.restrictScalars ℝ
  have hp : Envelope (fun T : Config G f => S.density β T U) :=
    Envelope.comp_env (f:=fun z : Config G f × Config G d => S.density β z.1 z.2)
      (g:=fun T : Config G f => (T,U)) (Push.GridApprox.den_env h) (measurable_id.prodMk measurable_const)
  have hi := Push.SectorMeasure.Env.smul_L1 hp hg
  unfold StepData.push
  calc _ = ∫ T, P (S.density β T U • g T) ∂prior G f := (P.integral_comp_comm hi).symm
       _ = _ := integral_congr_ae (ae_of_all _ fun T => P.map_smul _ _)

/-- At every true coarse field, one given complete fine readout transports
through the complete selected original output. -/
theorem numerator (S : Chosen K I M) (x : TestSpace J.tests) (L : Poly B →L[ℂ] ℂ) (U : Config G nc) :
    L ((S.output.output.leaf x).density U) = (op₀).push b₀ (fun T => L ((I.input.leaf x).density T)) U := by
  rw [←S.output.density x]
  exact chosen_slice op₀ (C.path.levels.transition_mass _ _ _) L (PositiveWilsonMarkedInput.selected S x) U

/-- The normalized *actual* selected defect is a single true conditional
average less the original nonlocal prescribed model. -/
theorem residual (hC : C.Makes) (S : Chosen K I M) (x : TestSpace J.tests) (L : Poly B →L[ℂ] ℂ)
    (g : Config G nf → ℂ) (hg : ∀ T, L ((I.input.leaf x).density T) = (W₁).eval T • g T) (U : Config G nc) :
    L (ActualSelectedModelIntegral.defect S x U) = actualAverage C (N:=datum.cutoff) g U-L (S.output.modelValue x U) := by
  let P := L.restrictScalars ℝ
  have h (a : ℝ) (v : Poly B) : L (a • v) = a • L v := P.map_smul _ _
  have hp := (Multi.AxisShift.chosen_positive hC.wilson datum.below.le U).ne'
  calc _ = ((W₀).eval U)⁻¹ • L ((W₀).eval U • ActualSelectedModelIntegral.defect S x U) := by rw [h,inv_smul_smul₀ hp]
       _ = ((W₀).eval U)⁻¹ • L ((S.output.output.leaf x).density U)-L (S.output.modelValue x U) := by
         rw [ActualSelectedModelIntegral.weighted_defect hC S x U,map_sub,smul_sub,h,inv_smul_smul₀ hp]
       _ = _ := by rw [numerator S x L U,funext hg,actualAverage_push]

end YM.Integration.SelectedWilsonForward
