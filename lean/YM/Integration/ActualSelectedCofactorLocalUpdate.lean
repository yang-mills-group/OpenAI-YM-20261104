import YM.Integration.NativeCoveredCofactorLocalUpdate
import YM.Integration.ActualSelectedCoveredCofactor

/-! Exact local-update factorization for the same selected output S.
No residual activity or flag-stability premise is added: original entry
locality is recovered from S's existing relative budget, and the complete
changed-flag indicator remains explicit. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualSelectedCofactorLocalUpdate
open Function Lattice Wilson RG Marker
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Script.Picnic OPE.Therm
open NativeCoveredCofactorLocalUpdate
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {forcedOrder : ℕ}

/-- The original, unnormalized physical entries have the native locality. -/
theorem original_entry_reads (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) :
    EntryReads (S.output.residual.leaf (testInclusion J.tests x)) :=
  entryReads_of_relative H.residual_price x

/-- All original rows and the same selected carrier are retained. The
remaining product is frozen only after isolating the exact flag fiber. -/
theorem cofactor_local_factorization (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U W : Config G (C.side datum.level datum.period)) (i : ℕ) (s : Finset ℕ)
    (hU : admitted S.output.carrier.rep U i s)
    (hOutside : sameOutside
      (S.output.carrier.rep.activities.forced i).support U W) :
    NativeTasteCoveredCofactor.cofactor
      (S.output.residual.leaf (testInclusion J.tests x)) W i s =
      if flags S.output.carrier.rep.p.threshold W =
          flags S.output.carrier.rep.p.threshold U
      then remainingProduct
        (S.output.residual.leaf (testInclusion J.tests x)) U i s else 0 :=
  NativeCoveredCofactorLocalUpdate.cofactor_local_factorization
    _ (original_entry_reads S H x) S.wellFormed.forced U W i s hU hOutside

/-- Single-link specialization; no assertion that a local update preserves flags. -/
theorem cofactor_update_factorization (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) (i : ℕ) (s : Finset ℕ)
    (hU : admitted S.output.carrier.rep U i s)
    (e : Edge (Site (C.side datum.level datum.period))) (u : G.El)
    (he : e.1 ∈ (S.output.carrier.rep.activities.forced i).support) :
    NativeTasteCoveredCofactor.cofactor
      (S.output.residual.leaf (testInclusion J.tests x)) (Function.update U e u) i s =
      if flags S.output.carrier.rep.p.threshold (Function.update U e u) =
          flags S.output.carrier.rep.p.threshold U
      then remainingProduct
        (S.output.residual.leaf (testInclusion J.tests x)) U i s else 0 :=
  NativeCoveredCofactorLocalUpdate.cofactor_update_factorization
    _ (original_entry_reads S H x) S.wellFormed.forced U i s hU e u he

end YM.Integration.ActualSelectedCofactorLocalUpdate
end
