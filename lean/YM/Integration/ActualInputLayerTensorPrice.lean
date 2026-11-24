import YM.Integration.NativeJointPayloadWidth
import YM.Integration.UniformJointPricePolynomial
import YM.Integration.ActualRunStationaryGeometry
import YM.Integration.FullQLocalNumericLogarithmicCost

/-! The true original input-layer bill pays every native joint-coordinate
marginal. Only the analytic width is capped; the original grading record,
its support reserve, all payloads and all list occurrences remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualInputLayerTensorPrice
open Function Filter Set Metric Lattice Wilson RG Precision Tree Exterior
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical ContDiff

private theorem input_cap_inverse {G : Gauge} {V : Type}
    {T : Run G} {J : Request V} (A : NumericSchedule T.family J) (i : ℕ) :
    (min (A.inputWidth i) 1)⁻¹ ≤ A.admittedCost i := by
  have hw := inv_pos.mpr (A.output_width_pos i)
  have hr := A.radius_loss_positive i
  have hb := A.cost_covers_widths i
  have hi : (A.inputWidth i)⁻¹ ≤ A.admittedCost i := by linarith
  by_cases h : A.inputWidth i ≤ 1
  · simpa only [min_eq_left h] using hi
  · simpa only [min_eq_right (le_of_not_ge h), inv_one] using A.admitted_cost_ge_one i

/-- Fixed constants and one tail precede every period, full layer record,
forest and tensor port. The original budget is used without a new purchase. -/
theorem layers_marginal {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} {J : Request V} (A : NumericSchedule T.family J) (n cap : ℕ) :
    let a := T.family.path.levels
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ᶠ i : ℕ in atTop, ∀ period : ℕ,
        let S := a.clock.op i period
        ∀ (p : BudgetPoint) (order : ℕ)
          (layers : List (Piece G (T.family.side (i + 1) period)))
          (_H : GradedVacuumLayers layers p order cap (A.inputWidth i) (A.admittedCost i))
          (B : Forest S.ratio),
        ∀ k : ℕ, k + 1 ≤ n → ∀ j : Fin (k + 1), ∀ i0 : Push.Uniform.Joint B G,
          (layers.map fun row => ∑ q : Fin k → Push.Uniform.Joint B G,
            ‖(((k + 1).factorial : ℝ)⁻¹) •
              entry (fun z => unmaskedPayload row.packet (fine G B z)) 0
                (Fin.insertNth j i0 q)‖).sum ≤
            C * (A.admittedCost i) ^ d := by
  dsimp only
  let a := T.family.path.levels
  obtain ⟨Z, hp⟩ := paint_supply G n
  obtain ⟨C, hC, e, hc⟩ := UniformJointPricePolynomial.bound G n cap Z
  refine ⟨C * (3 : ℝ) ^ e, by positivity, e + 1, ?_⟩
  filter_upwards [ActualRunStationaryGeometry.capped_geometry T hT,
    A.logarithmic_cost hG 7 1] with i hg hlog
  intro period p order layers H B k hk j i0
  let L := (a.clock.op i period).patch.L
  let μ : ℝ := min (A.inputWidth i) 1
  let W : ℝ := A.admittedCost i
  have hμ : 0 < μ := lt_min (A.input_width_pos i) (by norm_num)
  have hμone : μ ≤ 1 := min_le_right _ _
  have hμwidth : μ ≤ A.inputWidth i := min_le_left _ _
  have hW : 0 ≤ W := A.admitted_cost_nonnegative i
  have hWone : 1 ≤ W := A.admitted_cost_ge_one i
  have hμinv : μ⁻¹ ≤ W := input_cap_inverse A i
  have hL : (L.val : ℝ) ≤ W := by
    have hx := (hg period).2.2
    have hxinv := inv_pos.mpr (hg period).1
    have hnext := (Real.log_pos (a.fits.delayed (i + 1))).le
    simp only [pow_one] at hlog
    change 1 + (L.val : ℝ) + _ ≤ 7 * Real.log (a.clock.hatBeta i) at hx
    change 7 * Real.log (a.clock.hatBeta i) +
      7 * Real.log (a.clock.hatBeta (i + 1)) ≤ W at hlog
    linarith only [hx, hxinv, hnext, hlog]
  have hbase : 1 + (L.val : ℝ) + μ⁻¹ ≤ 3 * W := by linarith
  have hbase0 : 0 ≤ 1 + (L.val : ℝ) + μ⁻¹ := by positivity
  have hprice : NativeJointPayloadTensor.rankPrice G Z μ n cap *
      countCost (entryWidth n L μ / 2) *
      ((townCost G : ℝ) * countCost (weaker n (entryWidth n L μ))) ^ k ≤
      C * (3 * W) ^ e := by
    calc
      _ ≤ |NativeJointPayloadTensor.rankPrice G Z μ n cap *
          countCost (entryWidth n L μ / 2) *
          ((townCost G : ℝ) * countCost (weaker n (entryWidth n L μ))) ^ k| :=
        le_abs_self _
      _ ≤ C * (1 + (L.val : ℝ) + μ⁻¹) ^ e :=
        (hc L μ hμ hμone).2 k (by omega)
      _ ≤ C * (3 * W) ^ e :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase0 hbase e) hC.le
  calc
    _ ≤ W * (NativeJointPayloadTensor.rankPrice G Z μ n cap *
        countCost (entryWidth n L μ / 2) *
        ((townCost G : ℝ) * countCost (weaker n (entryWidth n L μ))) ^ k) :=
      NativeJointPayloadWidth.layers_marginal_le B H hp hμ hμwidth
        0 (by simp) hk j i0
    _ ≤ W * (C * (3 * W) ^ e) := mul_le_mul_of_nonneg_left hprice hW
    _ = (C * (3 : ℝ) ^ e) * W ^ (e + 1) := by rw [mul_pow, pow_succ]; ring

end YM.Integration.ActualInputLayerTensorPrice
end
