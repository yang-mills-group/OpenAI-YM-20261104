import YM.Integration.ActualRunStationaryCost
import YM.Integration.ActualRunStationaryGeometry
import YM.Integration.UniformJointPricePolynomial
import YM.Integration.NativeJointLoopTensor

/-! The complete original loop tensor with its original loopCap retained.
Only the remaining chart and coordinate factor is absorbed into the same
Run's logarithmic stamp. Every root and Signed channel is preserved. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunLoopTensorPrice
open Function Filter Set Metric Lattice RG Precision Tree Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical ContDiff

/-- The native loop budget is explicit; all other factors have fixed
logarithmic growth before cutoff, period, forest or tensor slot is chosen. -/
theorem loop_marginal {G : Gauge} (T : Run G)
    (hT : ActualRunNativeComponentRecipe.Attached T) (n : ℕ) :
    let a := T.family.path.levels
    ∃ A : ℝ, 0 < A ∧ ∃ d : ℕ,
      ∀ᶠ i : ℕ in atTop, ∀ N period : ℕ, i + 1 ≤ N →
        let S := a.clock.op i period
        ∀ B : Forest S.ratio,
          let F := fun z => loop (T.family.path.rep N period (i + 1)).path (fine G B z)
          ContDiffAt ℝ ω F 0 ∧
            ∀ k : ℕ, k + 1 ≤ n → ∀ j : Fin (k + 1),
              ∀ i0 : Push.Uniform.Joint B G,
              (∑ q : Fin k → Push.Uniform.Joint B G,
                ‖(((k + 1).factorial : ℝ)⁻¹) •
                  entry F 0 (Fin.insertNth j i0 q)‖) ≤
                a.clock.loopCap (i + 1) * (A * (Real.log (a.clock.hatBeta i)) ^ d) := by
  dsimp only
  let a := T.family.path.levels
  obtain ⟨Z, hp⟩ := paint_supply G n
  obtain ⟨_C0, _hC0, _d0, hpath⟩ :=
    ActualRunStationaryCost.stationary_log_cost T hT n Z 0 0
  obtain ⟨C, hC, e, hc⟩ := UniformJointPricePolynomial.bound G n 2 Z
  refine ⟨C * (7 : ℝ) ^ e, by positivity, e, ?_⟩
  filter_upwards [hpath, ActualRunStationaryGeometry.capped_geometry T hT] with i hi hg
  intro N period hN B
  let μ := NativeCappedPathBounds.cappedWidth (a.params (i + 1)).width
    (a.clock.J (i + 1))
  let L := (a.clock.op i period).patch.L
  let H := Real.log (a.clock.hatBeta i)
  let Λ := a.clock.loopCap (i + 1)
  have hP := (hi N period hN).1
  have hμ : 0 < μ := (hg period).1
  have hμone : μ ≤ 1 := (hg period).2.1
  have hΛ : 0 ≤ Λ := Extra.Iteration.Cost.nonneg hP.two
  have hz : (0 : Positions (Push.Uniform.Joint B G)) ∈ ball 0 1 := by simp
  have hloop := NativeJointLoopTensor.loop_beacons B hP hp 0 hz
  refine ⟨hloop.1, ?_⟩
  intro k hk j i0
  let E : ℝ := countCost (entryWidth n L μ / 2)
  let D : ℝ := (townCost G : ℝ) * countCost (weaker n (entryWidth n L μ))
  let Q : ℝ := ∑ r ∈ Finset.range (2 + 1), atomCost G Z μ n r
  have he : 0 ≤ E := (count_pos (half_pos (width_positive hμ n L))).le
  have hd : 0 ≤ D := by
    have hw : 0 < weaker n (entryWidth n L μ) := by
      exact div_pos (width_positive hμ n L) (by positivity)
    exact mul_nonneg (Nat.cast_nonneg _) (count_pos hw).le
  have hq : atomCost G Z μ n 2 ≤ Q :=
    Finset.single_le_sum (fun r _ => atomCost_nn hp hμ r) (by decide)
  have hcost : atomCost G Z μ n 2 * E * D ^ k ≤ C * (7 * H) ^ e := by
    calc
      _ ≤ Q * E * D ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq he) (pow_nonneg hd k)
      _ ≤ |Q * E * D ^ k| := le_abs_self _
      _ ≤ C * (1 + (L.val : ℝ) + μ⁻¹) ^ e :=
        (hc L μ hμ hμone).2 k (by omega)
      _ ≤ C * (7 * H) ^ e :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (hg period).2.2 e) hC.le
  calc
    _ ≤ NativeJointLoopTensor.loopCost G n Z μ Λ L * D ^ k :=
      NativeJointLoopTensor.loop_marginal B hP hp 0 hz hk j i0
    _ = Λ * (atomCost G Z μ n 2 * E * D ^ k) := by
      unfold NativeJointLoopTensor.loopCost E
      ring
    _ ≤ Λ * (C * (7 * H) ^ e) := mul_le_mul_of_nonneg_left hcost hΛ
    _ = Λ * ((C * (7 : ℝ) ^ e) * H ^ e) := by rw [mul_pow]; ring

end YM.Integration.ActualRunLoopTensorPrice
end
