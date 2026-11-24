import YM.Integration.WilsonPositionFiniteMSBank

/-! One fixed-order auxiliary lattice spacing. The physical cutoff and
period retain their original order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionAuxiliaryMesh
open Filter Function Set XSpace MS.Tide
open scoped Topology Classical

def floor (L : XSpace.Run) (p : ℕ) (t : ℝ) : ℕ :=
  ⌈-((p+1 : ℕ) : ℝ) * Real.log t / (mildG * Real.log L.ratio)⌉₊

private theorem ratio (L : XSpace.Run) : 1 < (L.ratio : ℝ) := by
  exact_mod_cast (show 1 < L.ratio from lt_of_lt_of_le (by decide) L.large)

theorem cost (L : XSpace.Run) (p : ℕ) {t : ℝ} (h : 0 < t) {i : ℕ} (high : floor L p t ≤ i) :
    (L.step i).spacing ^ mildG ≤ t ^ (p+1) := by
  have a := ratio L
  have e := Real.log_pos a
  have budget : (floor L p t : ℝ) ≤ (i : ℝ) := Nat.cast_le.mpr high
  have paid : -((p+1 : ℕ) : ℝ) * Real.log t / (mildG * Real.log L.ratio) ≤ (i : ℝ) :=
    (Nat.le_ceil _).trans budget
  have line := (div_le_iff₀ (mul_pos mild_p e)).mp paid
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos (L.step i).positive _) (pow_pos h _)).mp
  rw [Real.log_rpow (L.step i).positive, Real.log_pow]
  change mildG * Real.log (((L.ratio ^ i : ℕ) : ℝ)⁻¹) ≤ _
  rw [Real.log_inv,Nat.cast_pow,Real.log_pow]
  linarith only [line]

theorem grows (L : XSpace.Run) (p : ℕ) {t : ℝ → ℝ} (l : Filter ℝ)
    (pos : ∀ᶠ r in l, 0 < t r) (small : Tendsto t l (𝓝 0)) :
    Tendsto (fun r => floor L p (t r)) l atTop := by
  refine tendsto_atTop.2 fun k => ?_
  have psmall : Tendsto (fun r => (t r)^(p+1)) l (𝓝 0) := by
    simpa only [zero_pow (Nat.succ_ne_zero p)] using small.pow (p+1)
  have bound := psmall.eventually_lt_const (Real.rpow_pos_of_pos (L.step k).positive mildG)
  filter_upwards [pos,bound] with r positive less
  by_contra! short
  exact (not_lt_of_ge (cost L p positive short.le)) less

end YM.Integration.WilsonPositionAuxiliaryMesh
