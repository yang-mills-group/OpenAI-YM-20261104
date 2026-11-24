import YM.Integration.SelectedCofactorFlagRegion

/-! The actual uniform ordinary price subtracted from the complete selected
Wilson readout on the physical covered-region event. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorFlagRegionPrice
open Function Finset Set Filter MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate SelectedCofactorPacketIntegral
open SelectedCofactorConditionalSeries SelectedCofactorReplicatedFlags SelectedCofactorPhysicalMoment SelectedCofactorChamberMarginal
open scoped Classical BigOperators Topology
open SelectedCofactorPhysicalMoment SelectedCofactorChamberMarginal
variable {G : Gauge}
variable {V : Type} [DecidableEq V] [Fintype V] {B : Census V} {J : Request V}
variable {C : Family G} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F} {delta : ℝ} {order : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "W₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "Z₀" => partition G (C.side datum.cutoff datum.period) (C.path.β datum.cutoff datum.period datum.cutoff)

open ActualSelectedCoveredCofactor ActualSelectedModelIntegral

open ActualPolynomialContraction UniformPolynomialComparison
local notation "w₀" => (fun v => F.outputRadii v / F.kernelCosts v)
local notation "c₀" => MarkedPackets.uniformModelCost caps.packetRank (Fintype.card V) (K.geometry datum.level)
local notation "r₀" => Real.exp (Fintype.card V * ordinaryRate K I delta)

theorem ordinary (S : Chosen K I M) (H : Bounds S delta order)
    (x : IndependentTests J.tests) (U : Config G n₀) :
    Poly.price w₀ (S.output.modelValue (testInclusion J.tests x) U *
      (Poly.pass ((S.output.residual.leaf (testInclusion J.tests x)).log U) - 1)) ≤ c₀ * (r₀ - 1) := by
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
  apply (Poly.multiplication hw _ _).trans
  exact mul_le_mul (S.uniform_model_price x U) ht (Poly.nonnegative hw _)
    ((Poly.nonnegative hw _).trans (S.uniform_model_price x U))

private theorem sub_price (a b : ℂ) {r : ℝ} (h : ‖b‖ ≤ r) : ‖a - b‖ ≤ ‖a‖ + r := by
  have h₀ := norm_sub_le a b
  linarith

theorem readout (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (hFine : I.carrier.rep.eval = (C.path.rep datum.cutoff datum.period (datum.level + 1)).eval)
    (H : Bounds S delta order) (x : IndependentTests J.tests) (X : Set (Site n₀)) (U : Config G n₀)
    (hX : ∀ z ∈ flags S.output.carrier.rep.p.threshold U, z ∈ X)
    (L : Poly B →L[ℂ] ℂ) (hL : ∀ b, ‖L b‖ ≤ Poly.price w₀ b) :
    ‖L (((C.path.rep datum.cutoff datum.period datum.level).eval U)⁻¹ • rooted S x X (fun _ => True) U)‖ ≤
      ‖L (defect S (testInclusion J.tests x) U)‖ + c₀ * (r₀ - 1) := by
  let y := testInclusion J.tests x
  let a : Poly B := defect S y U
  let b : Poly B := S.output.modelValue y U * (Poly.pass ((S.output.residual.leaf y).log U) - 1)
  have hb : Poly.price w₀ b ≤ c₀ * (r₀ - 1) := ordinary S H x U
  have ht : ‖L b‖ ≤ c₀ * (r₀ - 1) := (hL b).trans hb
  rw [SelectedCofactorFlagRegion.normalized hG hC S hLate hFine H x X U hX,map_sub]
  change ‖L a - L b‖ ≤ ‖L a‖ + _
  exact sub_price (L a) (L b) ht

end YM.Integration.SelectedCofactorFlagRegionPrice
end
