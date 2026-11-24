import YM.Integration.ActualRunStationaryTensor
import YM.Integration.ActualRunStationaryGeometry
import YM.Integration.UniformJointPricePolynomial

/-! The full main/noise tensor, including every unfixed coordinate, is paid
by a fixed polynomial in the original logarithmic stamp. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStationaryTensorPrice
open Function Filter Lattice RG Precision Tree Push.Uniform Comparison.RG02
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical ContDiff

private theorem coordinate_power (G : Gauge) (n cap : ℕ) (Z : ℝ)
    (L : Side) (μ : ℝ) (k : ℕ) (hk : k ≤ n) :
    ((townCost G : ℝ) * countCost (weaker n (entryWidth n L μ))) ^ k ≤
      UniformJointPricePolynomial.majorant G n cap Z L μ := by
  let D : ℝ := (townCost G : ℝ) * countCost (weaker n (entryWidth n L μ))
  let A : ℝ := (∑ j ∈ Finset.range (cap + 1), atomCost G Z μ n j) *
    countCost (entryWidth n L μ / 2)
  have hb : 1 ≤ 1 + |D| := by linarith [abs_nonneg D]
  have hp : |D| ^ k ≤ (1 + |D|) ^ n :=
    (pow_le_pow_left₀ (abs_nonneg D)
      (show |D| ≤ 1 + |D| by linarith) k).trans (pow_le_pow_right₀ hb hk)
  change D ^ k ≤ (1 + |A|) * (1 + |D|) ^ n
  calc
    D ^ k ≤ |D| ^ k := by rw [← abs_pow]; exact le_abs_self _
    _ ≤ (1 + |D|) ^ n := hp
    _ ≤ (1 + |A|) * (1 + |D|) ^ n := by
      nlinarith [abs_nonneg A, pow_nonneg (show 0 ≤ 1 + |D| by positivity) n]

/-- Fixed constants precede every cutoff, period, forest, tag and tensor slot.
The score is the original full Surface, including both main and noise. -/
theorem surface_marginal {G : Gauge} (T : Run G)
    (hT : ActualRunNativeComponentRecipe.Attached T) (n : ℕ) (hn : 2 ≤ n) :
    let a := T.family.path.levels
    ∃ A : ℝ, 0 < A ∧ ∃ d : ℕ,
      ∀ᶠ i : ℕ in atTop, ∀ N period : ℕ, i + 1 ≤ N →
        let S := a.clock.op i period
        let Y := a.params (i + 1)
        ∀ (B : Forest S.ratio) (t : S.Choices),
          let F := Bulk.Surface S Y.clip
            (T.family.path.rep N period (i + 1)).path B t ∘ paint B G
          ContDiffAt ℝ ω F 0 ∧
            ∀ k : ℕ, k + 1 ≤ n → ∀ j : Fin (k + 1),
              ∀ i0 : Push.Uniform.Joint B G,
              (∑ q : Fin k → Push.Uniform.Joint B G,
                ‖(((k + 1).factorial : ℝ)⁻¹) •
                  entry F 0 (Fin.insertNth j i0 q)‖) ≤
                A * (Real.log (a.clock.hatBeta i)) ^ d := by
  dsimp only
  let a := T.family.path.levels
  obtain ⟨A, hA, d, hs⟩ := ActualRunStationaryTensor.surface_marginal T hT n hn
  obtain ⟨C, hC, e, hc⟩ := UniformJointPricePolynomial.polynomial G n 0 0
  refine ⟨A * C * (7 : ℝ) ^ e, by positivity, d + e, ?_⟩
  filter_upwards [hs, ActualRunStationaryGeometry.capped_geometry T hT] with i hi hg
  intro N period hN B t
  let μ := NativeCappedPathBounds.cappedWidth (a.params (i + 1)).width
    (a.clock.J (i + 1))
  let L := (a.clock.op i period).patch.L
  let H := Real.log (a.clock.hatBeta i)
  have hgeom := hg period
  have hμ : 0 < μ := hgeom.1
  have hH : 0 ≤ H := by
    have hL : (0 : ℝ) ≤ L.val := Nat.cast_nonneg _
    have hiμ : 0 < μ⁻¹ := inv_pos.mpr hμ
    have hgbase : 1 + (L.val : ℝ) + μ⁻¹ ≤ 7 * H := hgeom.2.2
    linarith only [hgbase, hL, hiμ]
  have hscore := hi N period hN B t
  refine ⟨hscore.1, ?_⟩
  intro k hk j i0
  have hbase : 0 ≤ 1 + (L.val : ℝ) + μ⁻¹ := by positivity
  have hcost := hc L μ hμ (hg period).2.1
  have hcoord :
      ((townCost G : ℝ) * countCost (weaker n (entryWidth n L μ))) ^ k ≤
        C * (7 * H) ^ e := by
    calc
      _ ≤ UniformJointPricePolynomial.majorant G n 0 0 L μ :=
        coordinate_power G n 0 0 L μ k (by omega)
      _ ≤ C * (1 + (L.val : ℝ) + μ⁻¹) ^ e := hcost
      _ ≤ C * (7 * H) ^ e :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hbase (hg period).2.2 e) hC.le
  calc
    _ ≤ (A * H ^ d) *
        ((townCost G : ℝ) * countCost (weaker n (entryWidth n L μ))) ^ k :=
      hscore.2 k hk j i0
    _ ≤ (A * H ^ d) * (C * (7 * H) ^ e) :=
      mul_le_mul_of_nonneg_left hcoord (mul_nonneg hA.le (pow_nonneg hH d))
    _ = (A * C * (7 : ℝ) ^ e) * H ^ (d + e) := by
      rw [mul_pow, pow_add]
      ring

end YM.Integration.ActualStationaryTensorPrice
end
