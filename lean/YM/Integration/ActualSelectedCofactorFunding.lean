import YM.Integration.ActualSelectedCoveredCofactor
import YM.Integration.LocalComparisonForcedFunding

/-! The existing physical clock pays the smallness condition in the exact
covered-cofactor identities. A single threshold depends only on the original
family and number of marked slots, before the order, datum, selected output,
or independent tests. The quantitative cofactor integral remains unpaid. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualSelectedCofactorFunding
open Function Filter MeasureTheory Lattice Wilson RG Marker
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Script.Picnic OPE.Therm
open ActualSelectedModelIntegral ActualSelectedCoveredCofactor
open scoped Classical BigOperators Topology

variable {G : Gauge}

/-- The original clock's threshold; no new schedule or family is chosen. -/
def start (C : Family G) (hG : G.Simple) (hC : C.Makes) (marks : ℕ) : ℕ :=
  (eventually_atTop.1 (actual_forced_smallness C hG hC marks)).choose

private theorem paid (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (marks N period m : ℕ) (hm : start C hG hC marks ≤ m)
    (hN : m < N) (order : ℕ) :
    C.path.levels.clock.forcedAllowance m + (marks : ℝ) *
      (forcedDivisor C m *
        Pert.Asymptotics.regulatorRun C N period (m + 1) ^ order) ≤ 1 :=
  (eventually_atTop.1 (actual_forced_smallness C hG hC marks)).choose_spec
    m hm N period hN order

variable {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {forcedOrder : ℕ}

local notation "P₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "μ₀" => prior G (C.side datum.level datum.period)
local notation "Z₀" => partition G (C.side datum.cutoff datum.period)
  (C.path.β datum.cutoff datum.period datum.cutoff)
local notation "w₀" => (fun v => F.outputRadii v / F.kernelCosts v)

/-- Full same-output weighted identity with its scalar guard supplied by
the actual clock, uniformly in all independent tests and field values. -/
theorem weighted_identity (hG : G.Simple) (hC : C.Makes)
    (S : Chosen K I M)
    (hLate : start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) :
    (P₀).eval U • defect S (testInclusion J.tests x) U =
      numerator S (testInclusion J.tests x) U := by
  exact ActualSelectedCoveredCofactor.weighted_identity hC S hFine H
    (paid C hG hC (Fintype.card V) datum.cutoff datum.period datum.level
      hLate datum.below forcedOrder) x U

/-- Actual input integrability gives integrability of the entire grouped
numerator. It does not require separate L1 bounds for its cofactors. -/
theorem numerator_integrable (hG : G.Simple) (hC : C.Makes)
    (S : Chosen K I M)
    (hLate : start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (hInput : Integrable (I.input.leaf (testInclusion J.tests x)).density
      (prior G (C.side (datum.level + 1) datum.period))) :
    Integrable (numerator S (testInclusion J.tests x)) μ₀ := by
  exact ActualSelectedCoveredCofactor.numerator_integrable hC S hFine H
    (paid C hG hC (Fintype.card V) datum.cutoff datum.period datum.level
      hLate datum.below forcedOrder) x hInput

/-- The full signed integral retains the original cutoff partition and
the same selected model; the forced smallness is derived. -/
theorem integral_identity (hG : G.Simple) (hC : C.Makes)
    (S : Chosen K I M)
    (hLate : start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    (∫ U, defect S (testInclusion J.tests x) U
      ∂scene C.path datum.cutoff datum.period datum.level) =
      Z₀⁻¹ • ∫ U, numerator S (testInclusion J.tests x) U ∂μ₀ := by
  exact ActualSelectedCoveredCofactor.integral_identity hC S hFine H
    (paid C hG hC (Fintype.card V) datum.cutoff datum.period datum.level
      hLate datum.below forcedOrder) x

/-- The price integral for the full polynomial, including every mode, uses
the original normalization. A bound on the cofactors is a separate estimate. -/
theorem price_integral_identity (hG : G.Simple) (hC : C.Makes)
    (S : Chosen K I M)
    (hLate : start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    (∫ U, Poly.price w₀ (defect S (testInclusion J.tests x) U)
      ∂scene C.path datum.cutoff datum.period datum.level) =
      Z₀⁻¹ * ∫ U, Poly.price w₀
        (numerator S (testInclusion J.tests x) U) ∂μ₀ := by
  exact ActualSelectedCoveredCofactor.price_integral_identity hC S hFine H
    (paid C hG hC (Fintype.card V) datum.cutoff datum.period datum.level
      hLate datum.below forcedOrder) x

end YM.Integration.ActualSelectedCofactorFunding
end
