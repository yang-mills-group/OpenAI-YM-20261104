import YM.Integration.SelectedCofactorPacketIntegral

/-! The signed forced numerator as a sum of physical complete-flag
fiber integrals on the original Wilson product Haar prior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorConditionalSeries

open Function Finset Filter MeasureTheory Lattice Wilson RG Marker Overlay
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate NativeCoveredCofactorHaar
open SelectedCofactorProductHaar SelectedCofactorPacketIntegral ActualSelectedCoveredCofactor
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {forcedOrder : ℕ}

local notation "μ₀" => prior G (C.side datum.level datum.period)
local notation "E₀" => Edge (Site (C.side datum.level datum.period))

/-- Retain the whole original polynomial minor and average the signed
local kernel on the unique complete-flag fiber admitted by this packet.
The integral is zero when the packet has no admitted link replacement. -/
def conditionedPacket (S : Chosen K I M) (x : IndependentTests J.tests)
    (p : ℕ × Finset ℕ) (e : E₀) (U : Config G (C.side datum.level datum.period)) : Poly B :=
  let P := S.output.carrier.rep
  let d := S.output.residual.leaf (testInclusion J.tests x)
  let W := fun u => update U e u
  if h : ∃ u, admitted P (W u) p.1 p.2 then
    (∫ u in flagFiber P (W h.choose) e, rowKernel S x p.1 (W u) ∂G.probHaar) *
      remainingProduct d (W h.choose) p.1 p.2 else 0

/-- Exact signed conditional mean at any link based in the distinguished
support, with a genuine integrable full row on each fiber. -/
theorem packet_link (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (p : ℕ × Finset ℕ) (e : E₀) (he : e.1 ∈ (S.output.carrier.rep.activities.forced p.1).support)
    (U : Config G (C.side datum.level datum.period)) :
    (∫ u, packet S x p (update U e u) ∂G.probHaar) = conditionedPacket S x p e U := by
  let P := S.output.carrier.rep
  let d := S.output.residual.leaf (testInclusion J.tests x)
  let W := fun u => update U e u
  unfold conditionedPacket
  dsimp only
  by_cases h : ∃ u, admitted P (W u) p.1 p.2
  · rw [dif_pos h]
    let A := flagFiber P (W h.choose) e
    let m := remainingProduct d (W h.choose) p.1 p.2
    have hco (u) : cofactor d (W u) p.1 p.2 = A.indicator (fun _ => m) u := by
      have hp := cofactor_eq_indicator d (ActualSelectedCofactorLocalUpdate.original_entry_reads S H x)
        S.wellFormed.forced (W h.choose) p.1 p.2 h.choose_spec e he u
      simpa only [W, Function.update_idem] using hp
    have hA : MeasurableSet A := flagFiber_measurable _ _
    have hi : IntegrableOn (fun u => rowKernel S x p.1 (W u)) A G.probHaar :=
      (rowKernel_link_integrable hC S H x p.1 U e).integrableOn
    calc
      _ = ∫ u, A.indicator (fun t => rowKernel S x p.1 (W t) * m) u ∂G.probHaar := by
        apply integral_congr_ae
        refine ae_of_all _ fun u => ?_
        change rowKernel S x p.1 (W u) * cofactor d (W u) p.1 p.2 = _
        rw [hco]
        by_cases hu : u ∈ A
        · simp only [Set.indicator_of_mem hu]
        simp only [Set.indicator_of_notMem hu, mul_zero]
      _ = ∫ u in A, rowKernel S x p.1 (W u) * m ∂G.probHaar := integral_indicator hA
      _ = _ := (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ m)).integral_comp_comm hi
  rw [dif_neg h]
  calc
    _ = ∫ _u : G.El, (0 : Poly B) ∂G.probHaar := by
      apply integral_congr_ae
      refine ae_of_all _ fun u => ?_
      change rowKernel S x p.1 (W u) * cofactor d (W u) p.1 p.2 = 0
      rw [cofactor_eq_if, if_neg (fun hu => h ⟨u,hu⟩), mul_zero]
    _ = _ := integral_zero _ _

/-- Native nonemptiness of every forced inventory supplies a link in its
full support. Any axis at an inventory site suffices for disintegration. -/
def rootEdge (S : Chosen K I M) (i : ℕ) : E₀ :=
  ((S.output.carrier.rep.activities.forced i).inventory_ne.choose, 0)

theorem rootEdge_mem (S : Chosen K I M) (i : ℕ) :
    (rootEdge S i).1 ∈ (S.output.carrier.rep.activities.forced i).support :=
  (S.output.carrier.rep.activities.forced i).inventory_sup
    (S.output.carrier.rep.activities.forced i).inventory_ne.choose_spec

def exteriorPacket (S : Chosen K I M) (x : IndependentTests J.tests) (p : ℕ × Finset ℕ) : Poly B :=
  ∫ y, conditionedPacket S x p (rootEdge S p.1) (anchor (rootEdge S p.1) y)
    ∂exteriorPrior G (rootEdge S p.1)

/-- The exterior signed conditional mean is a genuine Bochner integrand
even though its formula chooses an admitted value on each nonempty fiber. -/
theorem exterior_integrable (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) (p : ℕ × Finset ℕ) :
    Integrable (fun y => conditionedPacket S x p (rootEdge S p.1) (anchor (rootEdge S p.1) y))
      (exteriorPrior G (rootEdge S p.1)) :=
  (edge_disintegration (rootEdge S p.1) _ ((packet_absolute hC S H x).1 p)).1.congr
    (ae_of_all _ fun y => packet_link hC S H x p _ (rootEdge_mem S _) (anchor _ y))

/-- Product Haar Fubini integrates every exterior link and the complete
signed physical fiber at the selected root without conditioning the law. -/
theorem packet_integral (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) (p : ℕ × Finset ℕ) :
    (∫ U, packet S x p U ∂μ₀) = exteriorPacket S x p := by
  rw [(edge_disintegration (rootEdge S p.1) _ ((packet_absolute hC S H x).1 p)).2]
  exact integral_congr_ae (ae_of_all _ fun y =>
    packet_link hC S H x p _ (rootEdge_mem S _) (anchor _ y))

theorem forced_tsum (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) :
    (∑' p, packet S x p U) = forcedNumerator S (testInclusion J.tests x) U := by
  let d := S.output.residual.leaf (testInclusion J.tests x)
  let m := multiplier S x U
  let r := fun i => d.contents.each i U - scalarRow S.output.carrier.rep U i
  obtain ⟨D, hD, hDom⟩ := packet_dominated hC S H x
  have hp : Summable (fun p => packet S x p U) := hD.of_norm_bounded (fun p => hDom p U)
  obtain ⟨hs, hr, _⟩ := covered_series S H
    ((eventually_atTop.1 (actual_forced_smallness C hG hC (Fintype.card V))).choose_spec
      datum.level hLate datum.cutoff datum.period datum.below forcedOrder) x U
  letI : IsTopologicalSemiring (Poly B) :=
    { toContinuousAdd := inferInstance, toContinuousMul := inferInstance }
  rw [hp.tsum_prod]
  calc
    _ = ∑' i, m * (r i * ∑' s, cofactor d U i s) := by
      apply tsum_congr
      intro i
      change (∑' s, (m * r i) * cofactor d U i s) = _
      rw [(hs i).tsum_mul_left (m * r i), mul_assoc]
    _ = m * ∑' i, r i * ∑' s, cofactor d U i s := hr.tsum_mul_left m
    _ = _ := by
      change multiplier S x U * series d U = _
      simp only [ActualSelectedCoveredCofactor.forcedNumerator, multiplier, smul_mul_assoc, mul_assoc, d]

/-- Unconditional signed packet sums allow any given grouping of physical
addresses, including reflected or ancestor groups kept by a readout. -/
theorem grouped_forced_integral {T : Type*} (g : (ℕ × Finset ℕ) → T)
    (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    HasSum (fun t => ∑' p : {p // g p = t}, exteriorPacket S x p.val)
      (∫ U, forcedNumerator S (testInclusion J.tests x) U ∂μ₀) := by
  obtain ⟨hI, hA⟩ := packet_absolute hC S H x
  have h := hasSum_integral_of_summable_integral_norm hI hA
  simp_rw [packet_integral hC S H x] at h
  simp_rw [forced_tsum hG hC S hLate H x] at h
  exact h.tsum_fiberwise g

end YM.Integration.SelectedCofactorConditionalSeries
end
