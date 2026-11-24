import YM.Integration.SelectedCofactorCancellation
import YM.Integration.SelectedCofactorCancellationIntegral

/-! The physical one-mark term on the original Wilson scene. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorCancellationReadout

open Function Filter MeasureTheory Lattice Wilson RG Marker Overlay
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm
open ActualSelectedModelIntegral ActualSelectedCoveredCofactor
open SelectedCofactorCancellation NativeTasteCoveredCofactor
open scoped Classical BigOperators Topology

variable {G : Gauge}
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

/-- The full signed Bochner integral on the actual Wilson scene is
genuinely integrable from the selected output and the original clock. -/
theorem scene_defect_integrable (hG : G.Simple) (hC : C.Makes)
    (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) :
    Integrable (defect S (testInclusion J.tests x))
      (scene C.path datum.cutoff datum.period datum.level) := by
  apply actualScene_integrable_of_weighted C hC datum.below.le
  exact (SelectedCofactorCancellationIntegral.numerator_integrable hG hC S hLate hFine H x).congr
    (ae_of_all _ fun U => (ActualSelectedCofactorFunding.weighted_identity hG hC S hLate hFine H x U).symm)

/-- Every mode retains exactly the original disjoint cofactor partitions
in which the distinguished difference row owns at least one mark. -/
theorem forced_series_part (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests)
    (U : Config G (C.side datum.level datum.period)) (q : B.Mode) :
    let d := S.output.residual.leaf (testInclusion J.tests x)
    (series d U).part q = ∑' i, ∑ a : B.Mode, ∑ b : B.Mode,
      if a ≠ B.quiet ∧ Poly.merges a b q then
        (d.contents.each i U).part a * ∑' s, (cofactor d U i s).part b else 0 := by
  let d := S.output.residual.leaf (testInclusion J.tests x)
  have hot (i j) : (d.contents.marks i j).val.Nonempty :=
    (H.residual_price.budget.active x).articles.occurs i j
  have hs := covered_series S H
    ((eventually_atTop.1 (actual_forced_smallness C hG hC (Fintype.card V))).choose_spec
      datum.level hLate datum.cutoff datum.period datum.below forcedOrder) x U
  dsimp only
  rw [series, Poly.share hs.2.1]
  refine tsum_congr fun i => ?_
  rw [row_times_part d hot U i]
  simp_rw [Poly.share (hs.1 i)]
  rfl

def singletonRegular (S : Chosen K I M) (x : IndependentTests J.tests) (v : V)
    (U : Config G (C.side datum.level datum.period)) : ℂ :=
  (P₀).eval U • ((S.output.residual.leaf (testInclusion J.tests x)).log U).part (B.fire v)

/-- Each singleton retains the signed physical tagged row and every
admitted packet with its original signed vacuum rows. -/
def singletonForced (S : Chosen K I M) (x : IndependentTests J.tests) (v : V)
    (U : Config G (C.side datum.level datum.period)) : ℂ :=
  Real.exp (S.output.carrier.rep.exponent U) •
    singletonRows (S.output.residual.leaf (testInclusion J.tests x)) U v

private theorem regular_integrable_bound (hC : C.Makes) (S : Chosen K I M)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) (v : V) :
    Integrable (singletonRegular S x v) μ₀ ∧
    Poly.toll w₀ (B.fire v) * ‖Z₀⁻¹ • ∫ U, singletonRegular S x v U ∂μ₀‖ ≤
      Fintype.card V * ordinaryRate K I delta := by
  have hw (i) : 0 < w₀ i := div_pos (F.output_radius_positive i) (F.kernel_positive i)
  let E := (P₀).envelope (hC.wilson.represents datum.cutoff datum.period datum.level
    datum.below.le).good
  obtain ⟨a, ha, hd, hb⟩ := H.residual_price.physical_log_majorant F.kernel_positive x
    S.wellFormed.threshold
  have hm : Measurable (singletonRegular S x v) := E.meas.smul
    ((Poly.get (B.fire v)).continuous.measurable.comp
      (EngineeringWeightedReadout.regular_log_measurable H.residual_price x))
  have hpoint (U) : ‖singletonRegular S x v U‖ ≤ (P₀).eval U * (a.part (B.fire v)).re := by
    have hp := (Multi.AxisShift.chosen_positive hC.wilson datum.below.le U).le
    rw [singletonRegular, norm_smul, Real.norm_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left (hd (x, U) (B.fire v)) hp
  have hbI := (E.integrable μ₀).mul_const (a.part (B.fire v)).re
  have hr := hbI.mono' hm.aestronglyMeasurable (Eventually.of_forall hpoint)
  have hZ := Wilson.partition_pos (G := G) (n := C.side datum.cutoff datum.period)
    (C.path.β datum.cutoff datum.period datum.cutoff)
  have hcost : ‖Z₀⁻¹ • ∫ U, singletonRegular S x v U ∂μ₀‖ ≤ (a.part (B.fire v)).re := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hZ.le)]
    calc
      _ ≤ Z₀⁻¹ * ∫ U, (P₀).eval U * (a.part (B.fire v)).re ∂μ₀ :=
        mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans
          (integral_mono hr.norm hbI hpoint)) (inv_nonneg.mpr hZ.le)
      _ = _ := by rw [integral_mul_const, C.path.partition_eq hC.wilson datum.cutoff datum.period
                    datum.level datum.below.le, ← mul_assoc, inv_mul_cancel₀ hZ.ne', one_mul]
  refine ⟨hr, (mul_le_mul_of_nonneg_left hcost (Poly.worth hw _).le).trans ?_⟩
  rw [← ha.norm]
  exact (Poly.member hw _ a).trans hb

/-- In the one-mark coefficient, the ordinary signed remainder costs
only the linear log budget. Every forced root is still summed under its
original exponential and normalization. -/
theorem singleton_signed_remainder (hG : G.Simple) (hC : C.Makes)
    (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval =
      (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) (v : V) :
    Integrable (singletonForced S x v) μ₀ ∧
    Poly.toll w₀ (B.fire v) *
      ‖(∫ U, defect S (testInclusion J.tests x) U
          ∂scene C.path datum.cutoff datum.period datum.level).part (B.fire v) -
        Z₀⁻¹ • ∫ U, singletonForced S x v U ∂μ₀‖ ≤
      Fintype.card V * ordinaryRate K I delta := by
  let L := (Poly.get (B.fire v)).restrictScalars ℝ
  have hn := SelectedCofactorCancellationIntegral.numerator_integrable hG hC S hLate hFine H x
  obtain ⟨hr, hb⟩ := regular_integrable_bound hC S H x v
  have hp (U) : L (numerator S (testInclusion J.tests x) U) =
      singletonRegular S x v U + singletonForced S x v U :=
    numerator_singleton hG hC S hLate H x U v
  have hf : Integrable (singletonForced S x v) μ₀ :=
    ((L.integrable_comp hn).sub hr).congr (ae_of_all _ fun U =>
      by
        change L (numerator S (testInclusion J.tests x) U) - singletonRegular S x v U = _
        rw [hp, add_sub_cancel_left])
  refine ⟨hf, ?_⟩
  rw [ActualSelectedCofactorFunding.integral_identity hG hC S hLate hFine H x]
  change Poly.toll w₀ (B.fire v) * ‖L (Z₀⁻¹ • ∫ U, numerator S (testInclusion J.tests x) U ∂μ₀) -
    Z₀⁻¹ • ∫ U, singletonForced S x v U ∂μ₀‖ ≤ _
  rw [map_smul, ← L.integral_comp_comm hn,
    show (fun U => L (numerator S (testInclusion J.tests x) U)) =
      (fun U => singletonRegular S x v U + singletonForced S x v U) from funext hp,
    integral_add hr hf, smul_add, add_sub_cancel_right]
  exact hb

end YM.Integration.SelectedCofactorCancellationReadout
end
