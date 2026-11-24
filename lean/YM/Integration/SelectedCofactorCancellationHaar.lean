import YM.Integration.SelectedCofactorCancellation

/-! Conditional signed cancellation of a physical tagged row on its
complete original flag fiber, before multiplication by the pinned minor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorCancellationHaar

open Function Filter MeasureTheory Lattice Wilson RG Marker Overlay
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate NativeCoveredCofactorHaar
open SelectedCofactorCancellation
open scoped Classical BigOperators Topology

variable {G : Gauge}
variable {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {forcedOrder : ℕ}

/-- The genuine singleton activity of the distinguished physical row,
including its original exponent. -/
def taggedRow (S : Chosen K I M) (x : IndependentTests J.tests) (i : ℕ) (v : V)
    (U : Config G (C.side datum.level datum.period)) : ℂ :=
  (Real.exp (S.output.carrier.rep.exponent U) : ℂ) *
    ((S.output.residual.leaf (testInclusion J.tests x)).contents.each i U).part (B.fire v)

theorem tagged_row_haar_integrable (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) (i : ℕ) (v : V)
    (U : Config G (C.side datum.level datum.period)) (e : Edge (Site (C.side datum.level datum.period))) :
    Integrable (fun u => taggedRow S x i v (Function.update U e u)) G.probHaar := by
  let t := pullback (testInclusion J.tests) S.output.residual
  let d := priceNormalized (envelopeProduct F.kernelCosts) t
  have hs : Measurable (fun W => (d.leaf x).contents.each i W) := by
    unfold Bands.each
    refine Measurable.add ((Bands.sends _).measurable.comp
      (Complex.continuous_ofReal.measurable.comp (S.wellFormed.forced.meas i)))
      (Measurable.tsum fun j => ?_)
    exact (Bands.sends _).measurable.comp ((H.residual_price.budget.active x).articles.meas i j)
  have hr : Measurable (fun W => (t.leaf x).contents.each i W) := by
    have h : (fun W => (t.leaf x).contents.each i W) = fun W =>
        restoreEnvelope (envelopeProduct F.kernelCosts) (envelopeProduct_positive F.kernel_positive)
          ((d.leaf x).contents.each i W) := funext fun W =>
            (restoreEnvelope_each t F.kernelCosts F.kernel_positive x i W).symm
    rw [h]
    exact (restoreEnvelope (envelopeProduct F.kernelCosts)
      (envelopeProduct_positive F.kernel_positive)).continuous.measurable.comp hs
  let E := (ActualSelectedModelEnvelope.chosen_exponent_envelope hC S).exp
  have hm : Measurable (fun u => taggedRow S x i v (Function.update U e u)) :=
    ((Complex.continuous_ofReal.measurable.comp E.meas).mul
      ((Poly.get (B.fire v)).continuous.measurable.comp hr)).comp (update_continuous U e).measurable
  obtain ⟨c, hc⟩ := E.cost
  obtain ⟨_, _, _, hL⟩ := H.residual_price.native_each F.kernel_positive S.fixed_forced x
  obtain ⟨a, _, ha, _⟩ := hL i
  have hpoint (u : G.El) : ‖taggedRow S x i v (Function.update U e u)‖ ≤ c * a (B.fire v) := by
    rw [taggedRow, norm_mul, Complex.norm_real]
    exact mul_le_mul (hc (Function.update U e u)) (ha (x, Function.update U e u) (B.fire v))
      (norm_nonneg _) ((norm_nonneg _).trans (hc U))
  exact Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hpoint)

private theorem integrate_pinned (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) (i : ℕ) (s : Finset ℕ)
    (hU : admitted S.output.carrier.rep U i s)
    (e : Edge (Site (C.side datum.level datum.period)))
    (he : e.1 ∈ (S.output.carrier.rep.activities.forced i).support) (f : G.El → ℂ) :
    (∫ u, f u * pinnedVacuum S.output.carrier.rep (Function.update U e u) i s ∂G.probHaar) =
      (∫ u in flagFiber S.output.carrier.rep U e, f u ∂G.probHaar) *
        pinnedVacuum S.output.carrier.rep U i s := by
  let P := S.output.carrier.rep
  let d := S.output.residual.leaf (testInclusion J.tests x)
  let A := flagFiber P U e
  have hot (j k) : (d.contents.marks j k).val.Nonempty :=
    (H.residual_price.budget.active x).articles.occurs j k
  have hbase : (remainingProduct d U i s).part B.quiet = pinnedVacuum P U i s := by
    have h := cofactor_quiet d hot U i s
    rwa [cofactor_eq_if, if_pos hU] at h
  have hpoint (u) : f u * pinnedVacuum P (Function.update U e u) i s =
      A.indicator (fun t => f t * pinnedVacuum P U i s) u := by
    rw [← cofactor_quiet d hot, cofactor_eq_indicator d
      (ActualSelectedCofactorLocalUpdate.original_entry_reads S H x) S.wellFormed.forced U i s hU e he u]
    by_cases hu : u ∈ A
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hbase]
    rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, Poly.part_nil, mul_zero]
  rw [integral_congr_ae (ae_of_all _ hpoint), integral_indicator (flagFiber_measurable U e),
    integral_mul_const]

/-- The complete one-mark row on the link is its actual signed fiber
integral times the original scalar pinned minor. -/
theorem singleton_row_haar (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) (i : ℕ) (s : Finset ℕ)
    (hU : admitted S.output.carrier.rep U i s)
    (e : Edge (Site (C.side datum.level datum.period)))
    (he : e.1 ∈ (S.output.carrier.rep.activities.forced i).support) (v : V) :
    let d := S.output.residual.leaf (testInclusion J.tests x)
    let W := fun u => Function.update U e u
    (∫ u, (Real.exp (S.output.carrier.rep.exponent (W u)) : ℂ) *
      (((d.contents.each i (W u) - scalarRow S.output.carrier.rep (W u) i) *
        cofactor d (W u) i s).part (B.fire v)) ∂G.probHaar) =
      (∫ u in flagFiber S.output.carrier.rep U e, taggedRow S x i v (W u) ∂G.probHaar) *
        pinnedVacuum S.output.carrier.rep U i s := by
  let d := S.output.residual.leaf (testInclusion J.tests x)
  have hot (j k) : (d.contents.marks j k).val.Nonempty :=
    (H.residual_price.budget.active x).articles.occurs j k
  refine (integral_congr_ae (ae_of_all _ fun u => ?_)).trans
    (integrate_pinned S H x U i s hU e he (fun u => taggedRow S x i v (Function.update U e u)))
  rw [row_times_singleton d hot]
  exact (mul_assoc ..).symm

/-- The actual mass-scaled fluctuation on the complete flag fiber
integrates to zero before the signed remaining rows are estimated.
The identity holds also at zero fiber mass. -/
theorem centered_singleton_row_haar (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) (i : ℕ) (s : Finset ℕ)
    (hU : admitted S.output.carrier.rep U i s)
    (e : Edge (Site (C.side datum.level datum.period)))
    (he : e.1 ∈ (S.output.carrier.rep.activities.forced i).support) (v : V) :
    let A := flagFiber S.output.carrier.rep U e
    let f := fun u => taggedRow S x i v (Function.update U e u)
    (∫ u, (G.probHaar.real A • f u - ∫ t in A, f t ∂G.probHaar) *
      pinnedVacuum S.output.carrier.rep (Function.update U e u) i s ∂G.probHaar) = 0 := by
  let A := flagFiber S.output.carrier.rep U e
  let f := fun u => taggedRow S x i v (Function.update U e u)
  have hf : Integrable f G.probHaar := tagged_row_haar_integrable hC S H x i v U e
  change (∫ u, (G.probHaar.real A • f u - ∫ t in A, f t ∂G.probHaar) *
    pinnedVacuum S.output.carrier.rep (Function.update U e u) i s ∂G.probHaar) = 0
  have hleft : Integrable (fun u => G.probHaar.real A • f u) (G.probHaar.restrict A) :=
    Integrable.smul (G.probHaar.real A) hf.integrableOn
  have hright : Integrable (fun _ : G.El => ∫ t in A, f t ∂G.probHaar) (G.probHaar.restrict A) :=
    integrable_const _
  rw [integrate_pinned S H x U i s hU e he]
  change (∫ u in A, G.probHaar.real A • f u - ∫ t in A, f t ∂G.probHaar ∂G.probHaar) *
    pinnedVacuum S.output.carrier.rep U i s = 0
  rw [integral_sub hleft hright, integral_smul, setIntegral_const, sub_self, zero_mul]

/-- Two actual Haar replacements of the same distinguished link with
the same full flags cancel their antisymmetric tagged-row difference.
Every remaining vacuum row is the original pinned product. -/
theorem replicated_singleton_row_haar (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) (i : ℕ) (s : Finset ℕ)
    (hU : admitted S.output.carrier.rep U i s)
    (e : Edge (Site (C.side datum.level datum.period)))
    (he : e.1 ∈ (S.output.carrier.rep.activities.forced i).support) (v : V) :
    let A := flagFiber S.output.carrier.rep U e
    let W := fun u => Function.update U e u
    let f := fun u => taggedRow S x i v (W u)
    (∫ u, ∫ t in A, (f u - f t) * pinnedVacuum S.output.carrier.rep (W u) i s
      ∂G.probHaar ∂G.probHaar) = 0 := by
  let A := flagFiber S.output.carrier.rep U e
  let W := fun u => Function.update U e u
  let f := fun u => taggedRow S x i v (W u)
  have hf : Integrable f G.probHaar := tagged_row_haar_integrable hC S H x i v U e
  have hconst (u) : Integrable (fun _ : G.El => f u) (G.probHaar.restrict A) := integrable_const _
  have hin (u) : (∫ t in A, (f u - f t) * pinnedVacuum S.output.carrier.rep (W u) i s ∂G.probHaar) =
      (G.probHaar.real A • f u - ∫ t in A, f t ∂G.probHaar) *
        pinnedVacuum S.output.carrier.rep (W u) i s := by
    rw [integral_mul_const, integral_sub (hconst u) (hf.integrableOn (s := A)), setIntegral_const]
  exact (integral_congr_ae (ae_of_all _ hin)).trans
    (centered_singleton_row_haar hC S H x U i s hU e he v)

end YM.Integration.SelectedCofactorCancellationHaar
end
