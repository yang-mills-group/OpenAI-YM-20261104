import YM.Integration.SelectedCofactorProductHaar

/-! Absolute Bochner integration of every original signed rooted packet at
a fixed regulator, before summing or regrouping the physical rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorPacketIntegral

open Function Finset Filter MeasureTheory Lattice Wilson RG Marker Overlay
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate
open SelectedCofactorProductHaar ActualSelectedCoveredCofactor
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {forcedOrder : ℕ}

local notation "μ₀" => prior G (C.side datum.level datum.period)
local notation "w₀" => (fun v => F.outputRadii v / F.kernelCosts v)
local notation "c₀" => MarkedPackets.uniformModelCost caps.packetRank
  (Fintype.card V) (K.geometry datum.level)
local notation "r₀" => Real.exp (Fintype.card V * ordinaryRate K I delta)

def multiplier (S : Chosen K I M) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) : Poly B :=
  Real.exp (S.output.carrier.rep.exponent U) •
    (S.output.modelValue (testInclusion J.tests x) U *
      Poly.pass ((S.output.residual.leaf (testInclusion J.tests x)).log U))

/-- All field-dependent factors outside the pinned minor, with the
original difference at the distinguished address. -/
def rowKernel (S : Chosen K I M) (x : IndependentTests J.tests) (i : ℕ)
    (U : Config G (C.side datum.level datum.period)) : Poly B :=
  multiplier S x U * ((S.output.residual.leaf (testInclusion J.tests x)).contents.each i U -
    scalarRow S.output.carrier.rep U i)

def packet (S : Chosen K I M) (x : IndependentTests J.tests) (p : ℕ × Finset ℕ)
    (U : Config G (C.side datum.level datum.period)) : Poly B :=
  rowKernel S x p.1 U * cofactor (S.output.residual.leaf (testInclusion J.tests x)) U p.1 p.2

private theorem native_each_measurable (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) (i : ℕ) :
    Measurable (fun U => (S.output.residual.leaf (testInclusion J.tests x)).contents.each i U) := by
  let t := pullback (testInclusion J.tests) S.output.residual
  let d := priceNormalized (envelopeProduct F.kernelCosts) t
  have hs : Measurable (fun W => (d.leaf x).contents.each i W) := by
    unfold Bands.each
    refine Measurable.add ((Bands.sends _).measurable.comp
      (Complex.continuous_ofReal.measurable.comp (S.wellFormed.forced.meas i)))
      (Measurable.tsum fun j => ?_)
    exact (Bands.sends _).measurable.comp ((H.residual_price.budget.active x).articles.meas i j)
  have h : (fun W => (t.leaf x).contents.each i W) = fun W =>
      restoreEnvelope (envelopeProduct F.kernelCosts) (envelopeProduct_positive F.kernel_positive)
        ((d.leaf x).contents.each i W) := funext fun W =>
          (restoreEnvelope_each t F.kernelCosts F.kernel_positive x i W).symm
  change Measurable (fun W => (t.leaf x).contents.each i W)
  rw [h]
  exact (restoreEnvelope (envelopeProduct F.kernelCosts)
    (envelopeProduct_positive F.kernel_positive)).continuous.measurable.comp hs

private theorem scalar_measurable (S : Chosen K I M) (i : ℕ) :
    Measurable (fun U => (scalarRow S.output.carrier.rep U i : Poly B)) :=
  (Bands.sends _).measurable.comp (Complex.continuous_ofReal.measurable.comp (S.wellFormed.forced.meas i))

private theorem multiplier_measurable (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    Measurable (multiplier S x) := by
  have hg : Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1) ≠ 0 :=
    inv_ne_zero ((Real.sqrt_pos.2 (Overlay.beta_positive hC.wilson (Nat.succ_le_of_lt datum.below))).ne')
  have hm : Measurable (S.output.modelValue (testInclusion J.tests x)) := by
    change Measurable (fun U => S.output.modelValue (testInclusion J.tests x) U)
    simpa only [ProducedOutput.modelValue, S.same_model] using
      (M.prescribed.multiplier_envelope M.paid hg (testInclusion J.tests x)).meas
  exact (ActualSelectedModelEnvelope.chosen_exponent_envelope hC S).exp.meas.smul
    (hm.mul (H.residual_price.pass_log_envelope F.kernel_positive S.wellFormed.threshold x).meas)

theorem rowKernel_measurable (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) (i : ℕ) :
    Measurable (rowKernel S x i) :=
  (multiplier_measurable hC S H x).mul ((native_each_measurable S H x i).sub (scalar_measurable S i))

theorem packet_measurable (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) (p : ℕ × Finset ℕ) :
    Measurable (packet S x p) := by
  let P := S.output.carrier.rep
  let d := S.output.residual.leaf (testInclusion J.tests x)
  apply (rowKernel_measurable hC S H x p.1).mul
  simp_rw [cofactor_eq_if]
  have hset : MeasurableSet {U | admitted P U p.1 p.2} := by
    simp_rw [admitted_iff]
    exact (P.activities.admissible_borel P.p p.2).inter (MeasurableSet.const _)
  apply Measurable.ite hset _ measurable_const
  unfold remainingProduct CoveredSignedCofactors.mixed
  refine Finset.measurable_fun_prod _ fun j _ => ?_
  by_cases hj : j < p.1
  · simpa only [if_pos hj] using scalar_measurable S j
  simpa only [if_neg hj] using native_each_measurable S H x j

private theorem multiplier_price (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ U, Poly.price w₀ (multiplier S x U) ≤ c := by
  have hw v : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  obtain ⟨t, ht⟩ := (ActualSelectedModelEnvelope.chosen_exponent_envelope hC S).exp.cost
  obtain ⟨a, ha, hd, hb⟩ := H.residual_price.physical_log_majorant F.kernel_positive x S.wellFormed.threshold
  have hM : 0 ≤ c₀ := (Poly.nonnegative hw _).trans (S.uniform_model_price x 1)
  have hExp U : Real.exp (S.output.carrier.rep.exponent U) ≤ t :=
    (le_abs_self _).trans (ht U)
  refine ⟨t * (c₀ * r₀), mul_nonneg ((Real.exp_pos _).le.trans (hExp 1))
    (mul_nonneg hM (Real.exp_pos _).le), fun U => ?_⟩
  have hL : Poly.price w₀ ((S.output.residual.leaf (testInclusion J.tests x)).log U) ≤ Poly.price w₀ a := by
    unfold Poly.price
    apply sum_le_sum
    intro s _
    rw [ha.norm]
    exact mul_le_mul_of_nonneg_left (hd (x,U) s) (Poly.worth hw s).le
  have hP := (Poly.pass_budget hw _).trans (Real.exp_monotone (hL.trans hb))
  rw [multiplier, ActualPolynomialContraction.price_real_smul w₀ _ (Real.exp_pos _).le]
  apply mul_le_mul (hExp U) _ (Poly.nonnegative hw _) ((Real.exp_pos _).le.trans (hExp 1))
  exact (Poly.multiplication hw _ _).trans
    (mul_le_mul (S.uniform_model_price x U) hP (Poly.nonnegative hw _) hM)

/-- A single field-independent ℓ¹ sequence bounds the original difference,
the marked row and the vacuum row at every address. -/
private theorem native_rows (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) :
    ∃ a : ℕ → ℝ, (∀ i, 0 ≤ a i) ∧ Summable a ∧ ∀ i U,
      Poly.price w₀ ((S.output.residual.leaf (testInclusion J.tests x)).contents.each i U) ≤ a i ∧
      Poly.price w₀ (scalarRow S.output.carrier.rep U i : Poly B) ≤ a i ∧
      Poly.price w₀ ((S.output.residual.leaf (testInclusion J.tests x)).contents.each i U -
        scalarRow S.output.carrier.rep U i) ≤ a i := by
  have hw v : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  obtain ⟨b, hb, _, hL⟩ := H.residual_price.native_each F.kernel_positive S.fixed_forced x
  obtain ⟨k, hk, hK⟩ := Activities.K_total S.fixed_forced
  have hB i := (hL i).fares hw
  refine ⟨fun i => b i + k i, fun i => add_nonneg (hB i).1 (hK i).1, hb.add hk, fun i U => ?_⟩
  have h1 : Poly.price w₀ ((S.output.residual.leaf (testInclusion J.tests x)).contents.each i U) ≤ b i :=
    (hB i).2 (x,U)
  have h2 : Poly.price w₀ (scalarRow S.output.carrier.rep U i : Poly B) ≤ k i := by
    change Poly.price w₀ (Poly.send B.quiet _) ≤ _
    rw [Poly.solo, Poly.quiet_toll, one_mul, Complex.norm_real]
    exact (hK i).2 U
  refine ⟨h1.trans (le_add_of_nonneg_right (hK i).1), h2.trans (le_add_of_nonneg_left (hB i).1), ?_⟩
  rw [sub_eq_add_neg]
  apply (Poly.addition hw _ _).trans
  simpa only [Poly.price, Poly.part_neg, norm_neg] using add_le_add h1 h2

/-- Genuine Bochner integrability on every edge replacement, including
exterior fields of Haar measure zero. -/
theorem rowKernel_link_integrable (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) (i : ℕ)
    (U : Config G (C.side datum.level datum.period))
    (e : Edge (Site (C.side datum.level datum.period))) :
    Integrable (fun u => rowKernel S x i (update U e u)) G.probHaar := by
  have hw v : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  obtain ⟨a, _, _, hb⟩ := native_rows S H x
  obtain ⟨c, hc, hM⟩ := multiplier_price hC S H x
  obtain ⟨k, hk, hnorm⟩ := Poly.equivalent_norm (R := B) hw
  apply Integrable.of_bound ((rowKernel_measurable hC S H x i).comp
    (NativeCoveredCofactorHaar.update_continuous U e).measurable).aestronglyMeasurable
    (c * a i * k)
  refine ae_of_all _ fun u => (hnorm _).trans (mul_le_mul_of_nonneg_right ?_ hk)
  exact (Poly.multiplication hw _ _).trans (mul_le_mul (hM _) (hb i _).2.2 (Poly.nonnegative hw _) hc)

/-- The constants depend on the selected finite output. The coupon is
jointly summable over every physical root and every finite packet. -/
theorem packet_dominated (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    ∃ D : (ℕ × Finset ℕ) → ℝ, Summable D ∧ ∀ p U, ‖packet S x p U‖ ≤ D p := by
  have hw v : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  obtain ⟨a, ha, hs, h⟩ := native_rows S H x
  obtain ⟨c, hc, hM⟩ := multiplier_price hC S H x
  obtain ⟨k, hk, hnorm⟩ := Poly.equivalent_norm (R := B) hw
  refine ⟨fun p => (c * packetWeight a p) * k, ((packetWeight_summable ha hs).mul_left c).mul_right k,
    fun p U => (hnorm _).trans (mul_le_mul_of_nonneg_right ?_ hk)⟩
  let P := S.output.carrier.rep
  let d := S.output.residual.leaf (testInclusion J.tests x)
  rcases p with ⟨i,s⟩
  change Poly.price w₀ (rowKernel S x i U * cofactor d U i s) ≤ c * packetWeight a (i,s)
  rw [cofactor_eq_if]
  by_cases hU : admitted P U i s
  · rw [if_pos hU]
    have hi := hU.1
    have hroot : Poly.price w₀ (rowKernel S x i U) ≤ c * a i :=
      (Poly.multiplication hw _ _).trans (mul_le_mul (hM U) (h i U).2.2 (Poly.nonnegative hw _) hc)
    have hminor : Poly.price w₀ (remainingProduct d U i s) ≤ ∏ j ∈ s.erase i, a j := by
      unfold remainingProduct CoveredSignedCofactors.mixed
      apply (Poly.multiple hw _ _).trans
      apply Finset.prod_le_prod (fun j _ => Poly.nonnegative hw _)
      intro j _
      split
      · exact (h j U).2.1
      exact (h j U).1
    apply (Poly.multiplication hw _ _).trans
    apply (mul_le_mul hroot hminor (Poly.nonnegative hw _) (mul_nonneg hc (ha i))).trans_eq
    rw [mul_assoc, Finset.mul_prod_erase s a hi, packetWeight, if_pos hi]
  rw [if_neg hU, mul_zero, Poly.zero_price]
  apply mul_nonneg hc
  unfold packetWeight
  split
  · exact prod_nonneg fun i _ => ha i
  exact le_rfl

/-- Every signed polynomial packet is integrable, and the integral of
its norm is absolutely summable in the original joint index. -/
theorem packet_absolute (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    (∀ p, Integrable (packet S x p) μ₀) ∧
      Summable (fun p => ∫ U, ‖packet S x p U‖ ∂μ₀) := by
  obtain ⟨D, hD, hb⟩ := packet_dominated hC S H x
  have hI (p : ℕ × Finset ℕ) : Integrable (packet S x p) μ₀ := Integrable.of_bound (packet_measurable hC S H x p).aestronglyMeasurable
    (D p) (ae_of_all _ (hb p))
  refine ⟨hI, hD.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun p => ?_)⟩
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono (hI p).norm (integrable_const (D p)) (hb p)

end YM.Integration.SelectedCofactorPacketIntegral
end
