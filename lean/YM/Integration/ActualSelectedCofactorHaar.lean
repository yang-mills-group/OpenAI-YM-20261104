import YM.Integration.NativeCoveredCofactorHaar
import YM.Integration.ActualSelectedCofactorLocalUpdate

/-! Actual same-S Haar identities, with the original cutoff partition
retained literally. The surviving matching-flag probability is unpaid. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualSelectedCofactorHaar
open Function MeasureTheory Lattice Wilson RG Marker
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Script.Picnic OPE.Therm
open NativeCoveredCofactorLocalUpdate NativeCoveredCofactorHaar
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {forcedOrder : ℕ}

local notation "Z₀" => partition G (C.side datum.cutoff datum.period)
  (C.path.β datum.cutoff datum.period datum.cutoff)

theorem link_integrable (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) (i : ℕ) (s : Finset ℕ)
    (hU : admitted S.output.carrier.rep U i s)
    (e : Edge (Site (C.side datum.level datum.period)))
    (he : e.1 ∈ (S.output.carrier.rep.activities.forced i).support) :
    Integrable (fun u : G.El => NativeTasteCoveredCofactor.cofactor
      (S.output.residual.leaf (testInclusion J.tests x)) (Function.update U e u) i s)
      G.probHaar :=
  cofactor_link_integrable _
    (ActualSelectedCofactorLocalUpdate.original_entry_reads S H x)
    S.wellFormed.forced U i s hU e he

/-- Scalar local factors remain inside the exact matching-flag Haar integral;
the original Z is neither cancelled nor replaced. -/
theorem normalized_weighted_integral (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) (i : ℕ) (s : Finset ℕ)
    (hU : admitted S.output.carrier.rep U i s)
    (e : Edge (Site (C.side datum.level datum.period)))
    (he : e.1 ∈ (S.output.carrier.rep.activities.forced i).support)
    (f : G.El → ℂ) :
    Z₀⁻¹ • (∫ u, f u • NativeTasteCoveredCofactor.cofactor
      (S.output.residual.leaf (testInclusion J.tests x)) (Function.update U e u) i s
      ∂G.probHaar) =
      Z₀⁻¹ • ((∫ u in flagFiber S.output.carrier.rep U e, f u ∂G.probHaar) •
        remainingProduct (S.output.residual.leaf (testInclusion J.tests x)) U i s) := by
  exact congrArg (fun z : Poly B => Z₀⁻¹ • z)
    (weighted_cofactor_integral _
      (ActualSelectedCofactorLocalUpdate.original_entry_reads S H x)
      S.wellFormed.forced U i s hU e he f)

/-- The exact conditional flag probability is exposed, still divided by
the original cutoff Wilson partition. This is an identity, not a lower bound. -/
theorem normalized_integral (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) (i : ℕ) (s : Finset ℕ)
    (hU : admitted S.output.carrier.rep U i s)
    (e : Edge (Site (C.side datum.level datum.period)))
    (he : e.1 ∈ (S.output.carrier.rep.activities.forced i).support) :
    Z₀⁻¹ • (∫ u, NativeTasteCoveredCofactor.cofactor
      (S.output.residual.leaf (testInclusion J.tests x)) (Function.update U e u) i s
      ∂G.probHaar) =
      (Z₀⁻¹ * G.probHaar.real (flagFiber S.output.carrier.rep U e)) •
        remainingProduct (S.output.residual.leaf (testInclusion J.tests x)) U i s := by
  rw [cofactor_integral _
    (ActualSelectedCofactorLocalUpdate.original_entry_reads S H x)
    S.wellFormed.forced U i s hU e he, smul_smul]

end YM.Integration.ActualSelectedCofactorHaar
end
