import YM.Integration.ActualSelectedModelEnvelope
import YM.Integration.FullQLocalRetainedDefectEnvelope
import YM.Integration.FullQLocalRetainedModelPrice
import YM.Integration.FullQLocalResidualIntegrable
import YM.Integration.ActualPolynomialContraction
import YM.Integration.ActualScalarTransport

/-! Absolute integration of the entire selected model times its residual.
The normalization is the original Wilson partition. The complete flagged
mass remains explicit: this file does not assert that it is small. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualSelectedModelIntegral
open Function MeasureTheory Lattice Wilson RG Marker
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Script.Picnic OPE.Therm
open ActualSelectedModelEnvelope ActualPolynomialContraction
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}

local notation "P₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "μ₀" => prior G (C.side datum.level datum.period)
local notation "Z₀" => partition G (C.side datum.cutoff datum.period)
  (C.path.β datum.cutoff datum.period datum.cutoff)
local notation "w₀" => (fun v => F.outputRadii v / F.kernelCosts v)
local notation "c₀" => MarkedPackets.uniformModelCost caps.packetRank
  (Fintype.card V) (K.geometry datum.level)

/-- The full model factor is retained, including its nonlinear completion. -/
def defect (S : Chosen K I M) (x : TestSpace J.tests)
    (U : Config G (C.side datum.level datum.period)) : Poly B :=
  S.output.modelValue x U * S.output.residualError x U

/-- Native positivity cancels only the actual vacuum in the definition of
the residual. It does not identify or replace the chosen carrier. -/
theorem weighted_defect (hC : C.Makes) (S : Chosen K I M)
    (x : TestSpace J.tests) (U : Config G (C.side datum.level datum.period)) :
    (P₀).eval U • defect S x U =
      (S.output.output.leaf x).density U - (P₀).eval U • S.output.modelValue x U := by
  have hp : (P₀).eval U ≠ 0 :=
    (Multi.AxisShift.chosen_positive hC.wilson datum.below.le U).ne'
  have hf : (P₀).eval U •
      (S.output.modelValue x U *
        (((P₀).eval U)⁻¹ • (S.output.residual.leaf x).density U)) =
      (S.output.output.leaf x).density U := by
    rw [mul_smul_comm, smul_smul, mul_inv_cancel₀ hp, one_smul]
    exact (S.output.full x U).symm
  unfold defect ProducedOutput.residualError
  rw [mul_sub, mul_one, smul_sub, hf]

/-- Genuine input L1 and the paid complete model supply weighted L1 of
the whole defect. No integrability of a reciprocal vacuum is assumed. -/
theorem weighted_integrable (hC : C.Makes) (S : Chosen K I M)
    (x : TestSpace J.tests)
    (hInput : Integrable (I.input.leaf x).density
      (prior G (C.side (datum.level + 1) datum.period))) :
    Integrable (fun U => (P₀).eval U • defect S x U) μ₀ := by
  have hm : Integrable (fun U => (P₀).eval U • S.output.modelValue x U) μ₀ := by
    simpa only [ProducedOutput.modelValue, S.same_model] using
      M.prescribed.actual_model_weighted_integrable hC M.paid x
  have ho := S.output.output_integrable (datum := datum) x hInput
  exact (ho.sub hm).congr (ae_of_all _ fun U => (weighted_defect hC S x U).symm)

theorem scene_integrable (hC : C.Makes) (S : Chosen K I M)
    (x : TestSpace J.tests)
    (hInput : Integrable (I.input.leaf x).density
      (prior G (C.side (datum.level + 1) datum.period))) :
    Integrable (defect S x) (scene C.path datum.cutoff datum.period datum.level) :=
  actualScene_integrable_of_weighted C hC datum.below.le
    (weighted_integrable hC S x hInput)

variable {delta : ℝ} {forcedOrder : ℕ}

/-- One model bound works for all independently chosen test functions.
The full raw residual and its flagged exponential background are retained. -/
theorem weighted_price_bound (hC : C.Makes) (S : Chosen K I M)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder)
    (hSmall : C.path.levels.clock.forcedAllowance datum.level +
      (Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
          (datum.level + 1)) ^ forcedOrder) ≤ 1)
    (x : IndependentTests J.tests) (U : Config G (C.side datum.level datum.period)) :
    (P₀).eval U * Poly.price w₀ (defect S (testInclusion J.tests x) U) ≤
      c₀ * ((P₀).eval U * (Real.exp (Fintype.card V * ordinaryRate K I delta) - 1) +
        Real.exp (Fintype.card V * ordinaryRate K I delta) *
          flagNumerator S forcedOrder U) := by
  have hw : ∀ v, 0 < w₀ v :=
    fun v => div_pos (F.output_radius_positive v) (F.kernel_positive v)
  have hr := H.residual_density_error_price hSmall x U
  have hh := H.full_model_defect_price hSmall x U
  have hb := (Poly.nonnegative hw _).trans hr
  have h := hh.trans (mul_le_mul_of_nonneg_right (S.uniform_model_price x U) hb)
  have hv := S.output.output_vacuum hC datum.below hFine
  have hp := Multi.AxisShift.chosen_positive hC.wilson datum.below.le U
  rw [← price_real_smul w₀ _ hp.le, weighted_defect hC S]
  rw [hv, abs_of_pos hp, Complex.coe_smul] at h
  simpa only [flagNumerator, ForcedNormalization.flagPrice,
    mul_assoc, mul_comm, mul_left_comm] using h

/-- The exact original-scene integral of the absolute full defect is
controlled by the ordinary error and the explicit normalized flagged mass.
This is an integration theorem, not a proof of the remaining flag estimate. -/
theorem integral_bound (hC : C.Makes) (S : Chosen K I M)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder)
    (hSmall : C.path.levels.clock.forcedAllowance datum.level +
      (Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
          (datum.level + 1)) ^ forcedOrder) ≤ 1)
    (x : IndependentTests J.tests)
    (hInput : Integrable (I.input.leaf (testInclusion J.tests x)).density
      (prior G (C.side (datum.level + 1) datum.period))) :
    (∫ U, Poly.price w₀ (defect S (testInclusion J.tests x) U)
      ∂scene C.path datum.cutoff datum.period datum.level) ≤
      c₀ * ((Real.exp (Fintype.card V * ordinaryRate K I delta) - 1) +
        Real.exp (Fintype.card V * ordinaryRate K I delta) *
          flagMass S forcedOrder) := by
  have hP : Integrable (P₀).eval μ₀ :=
    ((P₀).envelope (hC.wilson.represents datum.cutoff datum.period datum.level
      datum.below.le).good).integrable _
  have hFlag := flagNumerator_integrable hC S forcedOrder
  have hPrice : Integrable
      (fun U => (P₀).eval U * Poly.price w₀ (defect S (testInclusion J.tests x) U)) μ₀ := by
    have h := price_integrable w₀
      (weighted_integrable hC S (testInclusion J.tests x) hInput)
    have he : (fun U => Poly.price w₀
        ((P₀).eval U • defect S (testInclusion J.tests x) U)) =
        fun U => (P₀).eval U * Poly.price w₀ (defect S (testInclusion J.tests x) U) := by
      funext U
      exact price_real_smul w₀ _
        (Multi.AxisShift.chosen_positive hC.wilson datum.below.le U).le
    rw [he] at h
    exact h
  have hOrd := hP.mul_const (Real.exp (Fintype.card V * ordinaryRate K I delta) - 1)
  have hForce := hFlag.const_mul (Real.exp (Fintype.card V * ordinaryRate K I delta))
  have hZ := Wilson.partition_pos (G := G)
    (n := C.side datum.cutoff datum.period) (C.path.β datum.cutoff datum.period datum.cutoff)
  rw [actualScene_formula C hC datum.below.le]
  change Z₀⁻¹ * (∫ U, (P₀).eval U *
    Poly.price w₀ (defect S (testInclusion J.tests x) U) ∂μ₀) ≤ _
  calc
    _ ≤ Z₀⁻¹ * ∫ U, c₀ *
        ((P₀).eval U * (Real.exp (Fintype.card V * ordinaryRate K I delta) - 1) +
          Real.exp (Fintype.card V * ordinaryRate K I delta) *
            flagNumerator S forcedOrder U) ∂μ₀ :=
      mul_le_mul_of_nonneg_left
        (integral_mono hPrice ((hOrd.add hForce).const_mul c₀)
          (weighted_price_bound hC S hFine H hSmall x))
        (inv_nonneg.mpr hZ.le)
    _ = _ := by
      rw [integral_const_mul, integral_add hOrd hForce,
        integral_mul_const, integral_const_mul,
        C.path.partition_eq hC.wilson datum.cutoff datum.period datum.level datum.below.le]
      unfold flagMass
      field_simp [hZ.ne']

end YM.Integration.ActualSelectedModelIntegral
end
