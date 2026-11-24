import YM.Integration.SelectedCofactorConditionalSeries

/-! Exact cancellation on the original product Haar scene for the
complete retained polynomial, with all signed packet sums justified. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorHaarExchange

open Function Finset Filter MeasureTheory Lattice Wilson RG Marker Overlay
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate NativeCoveredCofactorHaar
open SelectedCofactorProductHaar SelectedCofactorPacketIntegral SelectedCofactorConditionalSeries
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

/-- Two complete packet evaluations on the actual link update, retaining
the signed difference only when their original full flags agree. -/
def exchange (S : Chosen K I M) (x : IndependentTests J.tests) (p : ℕ × Finset ℕ)
    (e : E₀) (U : Config G (C.side datum.level datum.period)) (u : G.El) : Poly B :=
  if flags S.output.carrier.rep.p.threshold (update U e u) = flags S.output.carrier.rep.p.threshold U
  then packet S x p U - packet S x p (update U e u) else 0

def centered (S : Chosen K I M) (x : IndependentTests J.tests) (p : ℕ × Finset ℕ)
    (U : Config G (C.side datum.level datum.period)) : Poly B :=
  ∫ u, exchange S x p (rootEdge S p.1) U u ∂G.probHaar

private theorem exchange_measurable (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) (p : ℕ × Finset ℕ) (e : E₀) :
    Measurable (Function.uncurry (exchange S x p e)) := by
  let t := S.output.carrier.rep.p.threshold
  let Z := Config G (C.side datum.level datum.period) × G.El
  let W := fun z : Z => update z.1 e z.2
  have hW : Continuous W := continuous_fst.update e continuous_snd
  have hset : MeasurableSet {z : Z | flags t (W z) = flags t z.1} := by
    have h : {z : Z | flags t (W z) = flags t z.1} =
        ⋃ a : Support (C.side datum.level datum.period),
          {z : Z | flags t (W z) = a} ∩ {z : Z | flags t z.1 = a} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨fun he => ⟨_,he,rfl⟩, fun ⟨a,h₁,h₂⟩ => h₁.trans h₂.symm⟩
    rw [h]
    exact MeasurableSet.iUnion fun a => ((flags_measurable_eq t a).preimage hW.measurable).inter
      ((flags_measurable_eq t a).preimage measurable_fst)
  exact Measurable.ite hset (((packet_measurable hC S H x p).comp measurable_fst).sub
    ((packet_measurable hC S H x p).comp hW.measurable)) measurable_const

private theorem exchange_bound (S : Chosen K I M) (x : IndependentTests J.tests)
    {D : (ℕ × Finset ℕ) → ℝ} (hD : ∀ p U, ‖packet S x p U‖ ≤ D p)
    (p : ℕ × Finset ℕ) (e : E₀) (U : Config G (C.side datum.level datum.period)) (u : G.El) :
    ‖exchange S x p e U u‖ ≤ D p + D p := by
  unfold exchange
  split
  · exact (norm_sub_le _ _).trans (add_le_add (hD p U) (hD p _))
  rw [norm_zero]
  exact add_nonneg ((norm_nonneg _).trans (hD p U)) ((norm_nonneg _).trans (hD p U))

theorem centered_absolute (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    (∀ p, Integrable (centered S x p) μ₀) ∧ Summable (fun p => ∫ U, ‖centered S x p U‖ ∂μ₀) := by
  obtain ⟨D,hD,hb⟩ := packet_dominated hC S H x
  have hbound p U : ‖centered S x p U‖ ≤ D p + D p := by
    simpa only [centered, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := G.probHaar) (ae_of_all _ (exchange_bound S x hb p (rootEdge S p.1) U))
  have hI p : Integrable (centered S x p) μ₀ := Integrable.of_bound
    ((exchange_measurable hC S H x p (rootEdge S p.1)).stronglyMeasurable.integral_prod_right'
      (ν := G.probHaar)).aestronglyMeasurable _ (ae_of_all _ (hbound p))
  refine ⟨hI, (hD.add hD).of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) fun p => ?_⟩
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono (hI p).norm (integrable_const (D p + D p)) (hbound p)

/-- The omitted physical fluctuation is exactly the full-flag mass
times the actual packet minus its signed link integral on that fiber. -/
theorem centered_eq (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (p : ℕ × Finset ℕ)
    (U : Config G (C.side datum.level datum.period)) :
    let e := rootEdge S p.1
    let A := flagFiber S.output.carrier.rep U e
    centered S x p U = G.probHaar.real A • packet S x p U -
      ∫ u in A, packet S x p (update U e u) ∂G.probHaar := by
  let e := rootEdge S p.1
  let A := flagFiber S.output.carrier.rep U e
  obtain ⟨D,_,hb⟩ := packet_dominated hC S H x
  have hI : Integrable (fun u => packet S x p (update U e u)) G.probHaar :=
    Integrable.of_bound ((packet_measurable hC S H x p).comp (update_continuous U e).measurable).aestronglyMeasurable
      (D p) (ae_of_all _ fun u => hb p _)
  have hi (u) : exchange S x p e U u =
      A.indicator (fun v => packet S x p U - packet S x p (update U e v)) u := by
    by_cases hu : u ∈ A
    · rw [Set.indicator_of_mem hu]
      exact if_pos hu
    rw [Set.indicator_of_notMem hu]
    exact if_neg hu
  change (∫ u, exchange S x p e U u ∂G.probHaar) = _
  rw [integral_congr_ae (ae_of_all _ hi), integral_indicator (flagFiber_measurable U e),
    integral_sub (integrable_const _) (hI.integrableOn (s := A)), setIntegral_const]

omit [Fintype V] in
private theorem antisymmetric_integral {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) [SFinite ν]
    (f : Z → Z → Poly B) (hi : Integrable (uncurry f) (ν.prod ν))
    (ha : ∀ u t, f u t = -f t u) : (∫ u, ∫ t, f u t ∂ν ∂ν) = 0 := by
  let z := ∫ u, ∫ t, f u t ∂ν ∂ν
  have hz : z = -z := calc
    _ = ∫ t, ∫ u, f u t ∂ν ∂ν := integral_integral_swap hi
    _ = ∫ t, ∫ u, -f t u ∂ν ∂ν :=
      integral_congr_ae (ae_of_all _ fun t => integral_congr_ae (ae_of_all _ fun u => ha u t))
    _ = _ := by simp only [integral_neg, z]
  change z = 0
  ext q
  have hq := congrArg (fun a : Poly B => a.part q) hz
  change z.part q = (-z).part q at hq
  rw [Poly.part_neg] at hq
  change z.part q = 0
  linear_combination (1/2 : ℂ) * hq

omit [Fintype V] in
private theorem bounded_pair {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (ν : Measure Z) [IsFiniteMeasure ν] (f : Y → Z → Poly B) (k : Z → Y)
    (hm : Measurable (uncurry f)) (hk : Measurable k) (d : ℝ) (hb : ∀ v t, ‖f v t‖ ≤ d) :
    Integrable (fun z : Z × Z => f (k z.1) z.2) (ν.prod ν) := by
  have h : Measurable (fun z : Z × Z => (k z.1,z.2)) := (hk.comp measurable_fst).prodMk measurable_snd
  exact Integrable.of_bound (hm.comp h).aestronglyMeasurable d (ae_of_all _ fun z => hb (k z.1) z.2)

private theorem exchange_pair_integrable (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (p : ℕ × Finset ℕ) (e : E₀)
    (U : Config G (C.side datum.level datum.period)) :
    Integrable (fun z : G.El × G.El => exchange S x p e (update U e z.1) z.2) (G.probHaar.prod G.probHaar) := by
  obtain ⟨D,_,hb⟩ := packet_dominated hC S H x
  exact bounded_pair G.probHaar (exchange S x p e) (update U e) (exchange_measurable hC S H x p e)
    (update_continuous U e).measurable (D p + D p) (exchange_bound S x hb p e)

private theorem exchange_pair_neg (S : Chosen K I M) (x : IndependentTests J.tests) (p : ℕ × Finset ℕ)
    (e : E₀) (U : Config G (C.side datum.level datum.period)) (u t : G.El) :
    exchange S x p e (update U e u) t = -exchange S x p e (update U e t) u := by
  unfold exchange
  simp only [Function.update_idem]
  by_cases h : flags S.output.carrier.rep.p.threshold (update U e t) = flags S.output.carrier.rep.p.threshold (update U e u)
  · simp only [if_pos h, if_pos h.symm, neg_sub]
  simp only [if_neg h, if_neg (Ne.symm h), neg_zero]

private theorem centered_link (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (p : ℕ × Finset ℕ)
    (U : Config G (C.side datum.level datum.period)) :
    (∫ u, centered S x p (update U (rootEdge S p.1) u) ∂G.probHaar) = 0 :=
  antisymmetric_integral G.probHaar (fun u t => exchange S x p (rootEdge S p.1) (update U (rootEdge S p.1) u) t)
    (exchange_pair_integrable hC S H x p (rootEdge S p.1) U) (exchange_pair_neg S x p (rootEdge S p.1) U)

/-- Every original rooted packet has zero signed global exchange. -/
theorem centered_integral (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (p : ℕ × Finset ℕ) :
    (∫ U, centered S x p U ∂μ₀) = 0 := by
  rw [(edge_disintegration (rootEdge S p.1) _ ((centered_absolute hC S H x).1 p)).2]
  simp_rw [centered_link hC S H x p]
  exact integral_zero _ _

/-- The centered physical fluctuation cancels after any specified
countable packet selection, before the signed grouped readout is priced. -/
theorem centered_group_integral (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (Q : (ℕ × Finset ℕ) → Prop) :
    (∫ U, ∑' p : {p // Q p}, centered S x p.val U ∂μ₀) = 0 := by
  obtain ⟨hI,hA⟩ := centered_absolute hC S H x
  let T := {p : ℕ × Finset ℕ // Q p}
  have hs : Summable (fun p : T => ∫ U, ‖centered S x p.val U‖ ∂μ₀) := hA.subtype Q
  have hi : ∀ p : T, Integrable (centered S x p.val) μ₀ := fun p => hI p.val
  exact (integral_tsum_of_summable_integral_norm (F := fun p : T => centered S x p.val) hi hs).symm.trans
    ((tsum_congr fun p : T => centered_integral hC S H x p.val).trans tsum_zero)

/-- The remaining bill is evaluated only after the complete signed
conditional integrals are summed in each specified finite readout group. -/
theorem grouped_scene_price {T : Type*} [Fintype T] (g : (ℕ × Finset ℕ) → T)
    (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    let w := fun v => F.outputRadii v / F.kernelCosts v
    let Z := partition G (C.side datum.cutoff datum.period)
      (C.path.β datum.cutoff datum.period datum.cutoff)
    Poly.price w (∫ U, ActualSelectedModelIntegral.defect S (testInclusion J.tests x) U
      ∂scene C.path datum.cutoff datum.period datum.level) ≤
      MarkedPackets.uniformModelCost caps.packetRank (Fintype.card V) (K.geometry datum.level) *
        (Real.exp (Fintype.card V * ordinaryRate K I delta) - 1) +
      ∑ t : T, Poly.price w (Z⁻¹ • ∑' p : {p // g p = t}, exteriorPacket S x p.val) := by
  dsimp only
  have hg := (grouped_forced_integral g hG hC S hLate H x).tsum_eq
  rw [tsum_fintype] at hg
  have h := SelectedCofactorCancellationIntegral.signed_integral_price hG hC S hLate hFine H x
  rw [← hg, Finset.smul_sum] at h
  exact h.trans (add_le_add le_rfl (Poly.batch
    (fun v => div_pos (F.output_radius_positive v) (F.kernel_positive v)) Finset.univ _))

end YM.Integration.SelectedCofactorHaarExchange
end
