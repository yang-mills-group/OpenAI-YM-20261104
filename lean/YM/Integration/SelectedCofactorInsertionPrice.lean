import YM.Integration.SelectedCofactorJointBudget

/-! Native uniform price of the complete signed rooted insertion before restoring the original common vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorInsertionPrice

open Function Finset Filter MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate
open SelectedCofactorPacketIntegral SelectedCofactorConditionalSeries
open SelectedCofactorReplicatedFlags SelectedCofactorCommonVacuum SelectedCofactorJointBudget
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {forcedOrder : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "μ₀" => prior G n₀

local notation "w₀" => (fun v => F.outputRadii v / F.kernelCosts v)
local notation "c₀" => MarkedPackets.uniformModelCost caps.packetRank (Fintype.card V) (K.geometry datum.level)
local notation "r₀" => Real.exp (Fintype.card V * ordinaryRate K I delta)
local notation "ε₀" => ((Fintype.card V : ℝ) * (forcedDivisor C datum.level *
    Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1) ^ forcedOrder))

private theorem model_pass (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (U : Config G n₀) :
    Poly.price w₀ (S.output.modelValue (testInclusion J.tests x) U *
      Poly.pass ((S.output.residual.leaf (testInclusion J.tests x)).log U)) ≤ c₀ * r₀ := by
  have hw v : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  obtain ⟨a, ha, hd, hb⟩ := H.residual_price.physical_log_majorant F.kernel_positive x S.wellFormed.threshold
  have hL : Poly.price w₀ ((S.output.residual.leaf (testInclusion J.tests x)).log U) ≤ Poly.price w₀ a := by
    unfold Poly.price
    apply sum_le_sum
    intro s _
    rw [ha.norm]
    exact mul_le_mul_of_nonneg_left (hd (x,U) s) (Poly.worth hw s).le
  exact (Poly.multiplication hw _ _).trans (mul_le_mul (S.uniform_model_price x U)
    ((Poly.pass_budget hw _).trans (Real.exp_monotone (hL.trans hb))) (Poly.nonnegative hw _)
    ((Poly.nonnegative hw _).trans (S.uniform_model_price x U)))

/-- An arbitrary signed rooted group pays the retained support reserve once.
The bound contains the given model, ordinary correction and forced coupling order. -/
theorem insertion_price (hG : G.Simple) (hC : C.Makes) (S : Chosen K I M)
    (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (H : Bounds S delta forcedOrder) (x : IndependentTests J.tests) (X : Set (Site n₀))
    (Q : (ℕ × Finset ℕ) → Prop) (s : ℕ)
    (hq : ∀ a, (rootEdge S a.1).1 ∈ X → Q a →
      s ≤ coverNumber (A.outputNorm datum.level).B (S.output.carrier.rep.activities.forced a.1).support)
    (U : Config G n₀) : Poly.price w₀ (insertion S x X Q U) ≤
      (c₀ * r₀) * (Real.exp (-((A.outputNorm datum.level).supportExponent * s)) * ε₀) := by
  let ι := {a : ℕ × Finset ℕ // (rootEdge S a.1).1 ∈ X ∧ Q a}
  let D := S.output.residual.leaf (testInclusion J.tests x)
  have hSmall := (eventually_atTop.1 (actual_forced_smallness C hG hC (Fintype.card V))).choose_spec
    datum.level hLate datum.cutoff datum.period datum.below forcedOrder
  have hs := group_price H.residual_price F.kernel_positive S.fixed_forced hSmall x U
    (fun a => (rootEdge S a.1).1 ∈ X ∧ Q a) s (fun a ha => hq a ha.1 ha.2)
  have hseries : Summable (fun a : ι => term D U a.val) := hs.1
  have hz : rooted S x X Q U = multiplier S x U * ∑' a : ι, term D U a.val := calc
    _ = ∑' a : ι, multiplier S x U * term D U a.val :=
      tsum_congr fun a => mul_assoc _ _ _
    _ = _ := (hseries.hasSum.map
      ({ toFun := fun z => multiplier S x U * z, map_zero' := mul_zero _, map_add' := mul_add _ } : Poly B →+ Poly B)
      (continuous_const.mul continuous_id)).tsum_eq
  have he : insertion S x X Q U = (S.output.modelValue (testInclusion J.tests x) U * Poly.pass (D.log U)) *
      ∑' a : ι, term D U a.val := by
    rw [insertion,hz,multiplier,smul_mul_assoc,smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
  have hw v : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  rw [he]
  exact (Poly.multiplication hw _ _).trans (mul_le_mul (model_pass S H x U) hs.2
    (Poly.nonnegative hw _) (mul_nonneg ((Poly.nonnegative hw _).trans (S.uniform_model_price x U)) (Real.exp_pos _).le))

end YM.Integration.SelectedCofactorInsertionPrice
end
