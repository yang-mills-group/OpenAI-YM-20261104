import YM.Integration.ActualSelectedCofactorFunding

/-! The complete selected cofactor density is integrable from its own
finite output data. The uniform regular bill leaves the signed forced
integral on the original measure and with its original partition. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorCancellationIntegral

open Function Filter MeasureTheory Lattice Wilson RG Marker Overlay
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm
open ActualSelectedModelIntegral ActualSelectedModelEnvelope ActualSelectedCoveredCofactor
open ActualPolynomialContraction UniformPolynomialComparison
open scoped Classical BigOperators Topology

variable {G : Gauge}

private theorem deck_measurable {V : Type} [DecidableEq V] [Fintype V] {B : Census V}
    {n : Side} {P : Rep G n} (d : Deck B P) (hd : d.Active)
    (he : Measurable P.exponent) (hf : P.activities.ForcedFamily P.p) :
    Measurable d.density := by
  have hCluster : Measurable d.contents.cluster := by
    unfold Bands.cluster
    refine Measurable.tsum fun s => ?_
    unfold Bands.packet
    refine Measurable.ite (P.activities.admissible_borel P.p s)
      (Finset.measurable_fun_prod _ fun i _ => ?_) measurable_const
    unfold Bands.each
    refine Measurable.add ((Bands.sends _).measurable.comp
      (Complex.continuous_ofReal.measurable.comp (hf.meas i)))
      (Measurable.tsum fun j => ?_)
    exact (Bands.sends _).measurable.comp (hd.articles.meas i j)
  refine Measurable.smul (Complex.continuous_ofReal.measurable.comp
    (Real.continuous_exp.measurable.comp he)) ?_
  exact (Poly.pass_cont.measurable.comp ((d.contents.extra_meas hd.articles).add
    (measurable_const (a := d.captions.chord)))).mul hCluster

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

local notation "c₀" => MarkedPackets.uniformModelCost caps.packetRank
  (Fintype.card V) (K.geometry datum.level)
local notation "r₀" => Real.exp (Fintype.card V * ordinaryRate K I delta)

private theorem weighted_model_integrable (hC : C.Makes) (S : Chosen K I M)
    (x : IndependentTests J.tests) :
    Integrable (fun U => (P₀).eval U • S.output.modelValue (testInclusion J.tests x) U) μ₀ := by
  simpa only [ProducedOutput.modelValue, S.same_model] using
    M.prescribed.actual_model_weighted_integrable hC M.paid (testInclusion J.tests x)

/-- At every sufficiently late finite regulator, the existing selected
output bills give genuine integrability of the entire signed density. -/
theorem numerator_integrable (hG : G.Simple) (hC : C.Makes)
    (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    Integrable (numerator S (testInclusion J.tests x)) μ₀ := by
  have hw (v) : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  have ho := deck_measurable (S.output.output.leaf (testInclusion J.tests x))
    (S.output_active _) (chosen_exponent_envelope hC S).meas S.wellFormed.forced
  have hm := weighted_model_integrable hC S x
  have hN : AEStronglyMeasurable (numerator S (testInclusion J.tests x)) μ₀ :=
    (ho.aestronglyMeasurable.sub hm.aestronglyMeasurable).congr (ae_of_all _ fun U =>
      (weighted_defect hC S _ U).symm.trans
        (ActualSelectedCofactorFunding.weighted_identity hG hC S hLate hFine H x U))
  have hP : Integrable (P₀).eval μ₀ :=
    ((P₀).envelope (hC.wilson.represents datum.cutoff datum.period datum.level
      datum.below.le).good).integrable _
  have hMaj := ((hP.mul_const (r₀ - 1)).add
    ((flagNumerator_integrable hC S forcedOrder).const_mul r₀)).const_mul c₀
  obtain ⟨a, ha, hnorm⟩ := Poly.equivalent_norm (R := B) hw
  apply (hMaj.mul_const a).mono' hN
  apply Eventually.of_forall
  intro U
  apply (hnorm _).trans
  apply mul_le_mul_of_nonneg_right _ ha
  rw [← ActualSelectedCofactorFunding.weighted_identity hG hC S hLate hFine H x U,
    ActualPolynomialContraction.price_real_smul w₀ _ (Multi.AxisShift.chosen_positive hC.wilson datum.below.le U).le]
  exact weighted_price_bound hC S hFine H
    ((eventually_atTop.1 (actual_forced_smallness C hG hC (Fintype.card V))).choose_spec
      datum.level hLate datum.cutoff datum.period datum.below forcedOrder) x U

private theorem regular_price (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) :
    Poly.price w₀ (regularNumerator S (testInclusion J.tests x) U) ≤
      (P₀).eval U * (c₀ * (r₀ - 1)) := by
  have hw (v) : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  obtain ⟨a, ha, hd, hb⟩ := H.residual_price.physical_log_majorant F.kernel_positive x
    S.wellFormed.threshold
  have ht : Poly.price w₀ (Poly.pass ((S.output.residual.leaf (testInclusion J.tests x)).log U) - 1) ≤
      r₀ - 1 := by
    rw [pass_eq_one_add_tail, add_sub_cancel_left]
    apply le_trans _ ((tail_price_le ha hw).trans (sub_le_sub_right (Real.exp_monotone hb) 1))
    unfold Poly.price
    apply Finset.sum_le_sum
    intro q _
    rw [ha.tail.norm]
    exact mul_le_mul_of_nonneg_left ((hd.tail ha) (x, U) q) (Poly.worth hw q).le
  have hp := (Multi.AxisShift.chosen_positive hC.wilson datum.below.le U).le
  rw [regularNumerator, ActualPolynomialContraction.price_real_smul w₀ _ hp]
  apply mul_le_mul_of_nonneg_left _ hp
  apply (Poly.multiplication hw _ _).trans
  exact mul_le_mul (S.uniform_model_price x U) ht (Poly.nonnegative hw _)
    ((Poly.nonnegative hw _).trans (S.uniform_model_price x U))

private theorem regular_integrable (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    Integrable (regularNumerator S (testInclusion J.tests x)) μ₀ := by
  have hw (v) : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  have hm := weighted_model_integrable hC S x
  have ht := H.residual_price.regular_error_envelope F.kernel_positive S.wellFormed.threshold x
  have hmeas : AEStronglyMeasurable (regularNumerator S (testInclusion J.tests x)) μ₀ :=
    (hm.aestronglyMeasurable.mul ht.meas.aestronglyMeasurable).congr
      (ae_of_all _ fun U => smul_mul_assoc _ _ _)
  have hP := ((P₀).envelope (hC.wilson.represents datum.cutoff datum.period datum.level
    datum.below.le).good).integrable μ₀
  obtain ⟨a, ha, hnorm⟩ := Poly.equivalent_norm (R := B) hw
  exact (((hP.mul_const (c₀ * (r₀ - 1))).mul_const a).mono' hmeas
    (Eventually.of_forall fun U => (hnorm _).trans
      (mul_le_mul_of_nonneg_right (regular_price hC S H x U) ha)))

/-- The complete signed forced integral remains inside the original
normalization. Only the regular contribution is charged absolutely. -/
theorem signed_integral_remainder (hG : G.Simple) (hC : C.Makes)
    (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    Poly.price w₀ ((∫ U, defect S (testInclusion J.tests x) U
      ∂scene C.path datum.cutoff datum.period datum.level) -
      Z₀⁻¹ • ∫ U, ActualSelectedCoveredCofactor.forcedNumerator S (testInclusion J.tests x) U ∂μ₀) ≤
      c₀ * (r₀ - 1) := by
  have hw (v) : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  have hn := numerator_integrable hG hC S hLate hFine H x
  have hr := regular_integrable hC S H x
  have hf : Integrable (ActualSelectedCoveredCofactor.forcedNumerator S (testInclusion J.tests x)) μ₀ :=
    (hn.sub hr).congr (ae_of_all _ fun U => add_sub_cancel_left _ _)
  have hP := ((P₀).envelope (hC.wilson.represents datum.cutoff datum.period datum.level
    datum.below.le).good).integrable μ₀
  have hZ := Wilson.partition_pos (G := G) (n := C.side datum.cutoff datum.period)
    (C.path.β datum.cutoff datum.period datum.cutoff)
  rw [ActualSelectedCofactorFunding.integral_identity hG hC S hLate hFine H x]
  unfold numerator
  rw [integral_add hr hf, smul_add, add_sub_cancel_right,
    ActualPolynomialContraction.price_real_smul w₀ _ (inv_nonneg.mpr hZ.le)]
  calc
    _ ≤ Z₀⁻¹ * ∫ U, (P₀).eval U * (c₀ * (r₀ - 1)) ∂μ₀ :=
      mul_le_mul_of_nonneg_left ((ActualPolynomialContraction.price_integral_le hw hr).trans
        (integral_mono (ActualPolynomialContraction.price_integrable w₀ hr) (hP.mul_const _) (regular_price hC S H x)))
        (inv_nonneg.mpr hZ.le)
    _ = _ := by
      rw [integral_mul_const, C.path.partition_eq hC.wilson datum.cutoff datum.period
        datum.level datum.below.le, ← mul_assoc, inv_mul_cancel₀ hZ.ne', one_mul]

/-- A signed bound on the forced cofactor integral now suffices for
the entire finite comparison, with the model multiplier paid only once. -/
theorem signed_integral_price (hG : G.Simple) (hC : C.Makes)
    (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    Poly.price w₀ (∫ U, defect S (testInclusion J.tests x) U
      ∂scene C.path datum.cutoff datum.period datum.level) ≤
      c₀ * (r₀ - 1) + Poly.price w₀ (Z₀⁻¹ •
        ∫ U, ActualSelectedCoveredCofactor.forcedNumerator S (testInclusion J.tests x) U ∂μ₀) := by
  have hw (v) : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  have h := signed_integral_remainder hG hC S hLate hFine H x
  exact (le_of_eq (congrArg (Poly.price w₀) (sub_add_cancel _ _).symm)).trans
    ((Poly.addition hw _ _).trans (add_le_add h (le_refl _)))

end YM.Integration.SelectedCofactorCancellationIntegral
end
