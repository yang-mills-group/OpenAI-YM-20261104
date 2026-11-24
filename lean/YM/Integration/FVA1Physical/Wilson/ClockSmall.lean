import YM.Integration.FVA1Physical.Wilson.ScenePrice

/-! Uniform smallness of every measured coupling after a common stage cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter RG Lattice YM.Wilson MSbar MSbar.Heath.Stock
open scoped Topology
variable {G : Gauge} (A : History G)

theorem actual_clock_small {q d : ℝ} (hq : 0 < q) (hd : 0 < d)
    (hg : G.Simple) (sel : A.Selected) :
    ∀ᶠ k : ℕ in atTop, ∀ i, k ≤ i → ∀ N n, i ≤ N → cue (A.rep N n i).beta ^ q ≤ d := by
  have grows := (tendsto_rpow_atTop (half_pos hq)).comp
    ((Multi.Wage.hat_tend hg A.levels).atTop_mul_const (by norm_num : 0 < (1/2:ℝ)))
  obtain ⟨k₀,H⟩ := eventually_atTop.mp (grows.eventually_ge_atTop d⁻¹)
  filter_upwards [eventually_ge_atTop k₀] with k large
  intro i ki N n hi
  let y := A.levels.clock.hatBeta i
  let β := (A.rep N n i).beta
  have lo : y/2 ≤ β := (sel.represents N n i hi).band.1
  have base : 1 < y := A.levels.fits.delayed i
  have hp : 0 < y/2 := half_pos (zero_lt_one.trans base)
  have hβ : 0 < β := hp.trans_le lo
  have high : d⁻¹ ≤ (y*(1/2))^(q/2) := H i (large.trans ki)
  rw [show y*(1/2)=y/2 by ring] at high
  have hh := high.trans (Real.rpow_le_rpow hp.le lo (half_pos hq).le)
  change ((Real.sqrt β)⁻¹)^q ≤ d
  rw [Real.sqrt_eq_rpow,←Real.rpow_neg hβ.le,←Real.rpow_mul hβ.le,show -(1/2:ℝ)*q= -(q/2) by ring,
    Real.rpow_neg hβ.le]
  exact (inv_anti₀ (inv_pos.mpr hd) hh).trans_eq (inv_inv d)
end YM.Integration.FVA1Physical.Wilson
