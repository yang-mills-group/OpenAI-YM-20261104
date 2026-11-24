import YM.Integration.NativeTasteCoveredCofactor
import YM.Integration.ActualSelectedModelIntegral

/-! The full selected defect as an exact physical covered-cofactor numerator.
The same selected carrier, complete model, all remaining flags, and original
cutoff partition are retained. No estimate on a cofactor ratio is assumed. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualSelectedCoveredCofactor
open Function MeasureTheory Lattice Wilson RG Marker
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Script.Picnic OPE.Therm
open ActualSelectedModelIntegral ActualPolynomialContraction
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

/-- The complete regular/caption contribution, multiplied by the same model. -/
def regularNumerator (S : Chosen K I M) (x : TestSpace J.tests)
    (U : Config G (C.side datum.level datum.period)) : Poly B :=
  (P₀).eval U • (S.output.modelValue x U *
    (Poly.pass ((S.output.residual.leaf x).log U) - 1))

/-- Every signed covered cofactor remains inside the original physical
exponential and the complete selected model and regular/caption factors. -/
def forcedNumerator (S : Chosen K I M) (x : TestSpace J.tests)
    (U : Config G (C.side datum.level datum.period)) : Poly B :=
  Real.exp (S.output.carrier.rep.exponent U) •
    (S.output.modelValue x U *
      (Poly.pass ((S.output.residual.leaf x).log U) *
        NativeTasteCoveredCofactor.series (S.output.residual.leaf x) U))

def numerator (S : Chosen K I M) (x : TestSpace J.tests)
    (U : Config G (C.side datum.level datum.period)) : Poly B :=
  regularNumerator S x U + forcedNumerator S x U

variable {delta : ℝ} {forcedOrder : ℕ}

/-- Absolute convergence and the exact signed expansion come from the
existing row budgets. No support, marked alternative or remaining flag is
discarded, and no free-gas denominator is introduced. -/
theorem covered_series (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (hSmall : C.path.levels.clock.forcedAllowance datum.level +
      (Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
          (datum.level + 1)) ^ forcedOrder) ≤ 1)
    (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) :
    (∀ i, Summable (NativeTasteCoveredCofactor.cofactor
      (S.output.residual.leaf (testInclusion J.tests x)) U i)) ∧
    Summable (fun i =>
      ((S.output.residual.leaf (testInclusion J.tests x)).contents.each i U -
        NativeTasteCoveredCofactor.scalarRow S.output.carrier.rep U i) *
      ∑' s, NativeTasteCoveredCofactor.cofactor
        (S.output.residual.leaf (testInclusion J.tests x)) U i s) ∧
    forcedClusterError (S.output.residual.leaf (testInclusion J.tests x)) U =
      NativeTasteCoveredCofactor.series
        (S.output.residual.leaf (testInclusion J.tests x)) U := by
  exact NativeTasteCoveredCofactor.relative_series H.residual_price
    F.kernel_positive S.fixed_forced hSmall x U

/-- The actual physical vacuum multiplies the full M*E. Its only expansion
is into the original regular piece and the signed compulsory cofactor sum. -/
theorem weighted_identity (hC : C.Makes) (S : Chosen K I M)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder)
    (hSmall : C.path.levels.clock.forcedAllowance datum.level +
      (Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
          (datum.level + 1)) ^ forcedOrder) ≤ 1)
    (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) :
    (P₀).eval U • defect S (testInclusion J.tests x) U =
      numerator S (testInclusion J.tests x) U := by
  have hs := (covered_series S H hSmall x U).2.2
  have hd := density_error_split
    (S.output.residual.leaf (testInclusion J.tests x)) U
  have hv := S.output.output_vacuum hC datum.below hFine
  rw [hv, hs] at hd
  have hm := congrArg
    (fun Z : Poly B => S.output.modelValue (testInclusion J.tests x) U * Z) hd
  rw [weighted_defect hC S]
  have hout :
      (S.output.output.leaf (testInclusion J.tests x)).density U =
      S.output.modelValue (testInclusion J.tests x) U *
        (S.output.residual.leaf (testInclusion J.tests x)).density U :=
    S.output.full (testInclusion J.tests x) U
  rw [hout]
  simpa only [numerator, regularNumerator, forcedNumerator, mul_sub,
    mul_add, mul_one, mul_smul_comm, Complex.coe_smul] using hm

/-- Genuine input L1 supplies L1 of the complete cofactor numerator through
its exact equality to the full selected defect. Separate absolute cofactor
integrability is not asserted. -/
theorem numerator_integrable (hC : C.Makes) (S : Chosen K I M)
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
    Integrable (numerator S (testInclusion J.tests x)) μ₀ := by
  exact (weighted_integrable hC S (testInclusion J.tests x) hInput).congr
    (ae_of_all _ fun U => weighted_identity hC S hFine H hSmall x U)

/-- The normalized integral uses the original cutoff Wilson partition.
The signed series remains grouped inside the field integral. -/
theorem integral_identity (hC : C.Makes) (S : Chosen K I M)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder)
    (hSmall : C.path.levels.clock.forcedAllowance datum.level +
      (Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
          (datum.level + 1)) ^ forcedOrder) ≤ 1)
    (x : IndependentTests J.tests) :
    (∫ U, defect S (testInclusion J.tests x) U
      ∂scene C.path datum.cutoff datum.period datum.level) =
      Z₀⁻¹ • ∫ U, numerator S (testInclusion J.tests x) U ∂μ₀ := by
  rw [actualScene_formula C hC datum.below.le]
  congr 1
  exact integral_congr_ae
    (ae_of_all _ fun U => weighted_identity hC S hFine H hSmall x U)

/-- The complete absolute polynomial price has the same original
normalization. This is an identity, not a bound on the covered cofactors. -/
theorem price_integral_identity (hC : C.Makes) (S : Chosen K I M)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder)
    (hSmall : C.path.levels.clock.forcedAllowance datum.level +
      (Fintype.card V : ℝ) * (forcedDivisor C datum.level *
        (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period
          (datum.level + 1)) ^ forcedOrder) ≤ 1)
    (x : IndependentTests J.tests) :
    (∫ U, Poly.price w₀ (defect S (testInclusion J.tests x) U)
      ∂scene C.path datum.cutoff datum.period datum.level) =
      Z₀⁻¹ * ∫ U, Poly.price w₀
        (numerator S (testInclusion J.tests x) U) ∂μ₀ := by
  rw [actualScene_formula C hC datum.below.le]
  change Z₀⁻¹ * (∫ U, (P₀).eval U *
    Poly.price w₀ (defect S (testInclusion J.tests x) U) ∂μ₀) = _
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun U => by
    change (P₀).eval U * Poly.price w₀ (defect S (testInclusion J.tests x) U) =
      Poly.price w₀ (numerator S (testInclusion J.tests x) U)
    rw [← price_real_smul w₀ _
      (Multi.AxisShift.chosen_positive hC.wilson datum.below.le U).le,
      weighted_identity hC S hFine H hSmall x U]

end YM.Integration.ActualSelectedCoveredCofactor
end
