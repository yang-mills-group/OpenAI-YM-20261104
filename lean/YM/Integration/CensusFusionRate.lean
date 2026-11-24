import YM.Integration.WilsonLimitConstruction.FundedCensusVacuum

/-! The original two-tree reserve and its nonlinear hard fusion charge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CensusFusionRate

open Lattice Wilson RG RG.Shoot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG01Estimate RG01Estimate.CensusStep
open AnalyticBridge VerifiedReset Next.Scheduling Pressure Push Push.PriceCompiler
open Progress.DirectedRecipe

variable {G : Gauge}

/-- Keep the original factor of eight in the income certificate. -/
theorem original (R : Run G) (m : ℕ) :
    hardCost R.kit m ≤ (1/8 : ℝ)*R.alloy.B.a.clock.forcedAllowance m := by
  let a := R.alloy.B.a
  let β := a.clock.hatBeta (m+1)
  have hp : β ∈ Shoot.band a (m+1) := by
    have hr : 1 < β := a.fits.delayed _
    exact ⟨by change β/2 ≤ β; linarith, by change β ≤ 2*β; linarith⟩
  let j := a.clock.J (m+1)
  let i := a.clock.J m
  let y := betaF G (a.clock.hatBeta m) (R.rolls.L j)
  have heq : β = y := PriceCompiler.beta_eq R.alloy.B.valid m
  have h := R.kit.pledging.conducts.income.earns j i (step_paid a m)
    (a.clock.hatBeta m) (R.alloy.B.valid.pays m) β
    (show inBand y β from heq ▸ trial_in hp)
  change hardCost R.kit m ≤ (1/8 : ℝ)*(R.kit.scout j i).pair.strong y β at h
  rw [← heq] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (VacuumPrices.forecast_allowance R.kit (Nat.lt_succ_self m) hp) (by norm_num))

/-- A coarse block with a small soft bill can fuse its original hard
source at the same forced allowance. -/
theorem rates (B : ℕ) {γ w C : ℝ} (hγ : 0 < γ) (hw : 0 ≤ w)
    (he : w ≤ (1/8 : ℝ)*γ) (hC : 0 ≤ C)
    (hs : ((B+B+1 : ℕ) : ℝ)^4*C ≤ (1/32 : ℝ))
    (hflat : 4*((B+B+1 : ℕ) : ℝ)^4*γ ≤ 1) :
    ∃ κ, Payments.Rates B γ w C κ := by
  let D : ℝ := ((B+B+1 : ℕ) : ℝ)^4
  let t := 4*D*γ
  let k := -Real.log t
  have hD : 1 ≤ D := by
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ B+B+1 by omega))
  have hd : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have ht : 0 < t := by dsimp only [t]; positivity
  have hk : 0 ≤ k := neg_nonneg.mpr (Real.log_nonpos ht.le hflat)
  have hx : Real.exp k = t⁻¹ := by rw [show k = -Real.log t from rfl, Real.exp_neg, Real.exp_log ht]
  have hy : Real.exp (-k) = t := by rw [show -k = Real.log t by dsimp only [k]; ring, Real.exp_log ht]
  let X := Payments.inflation w C k
  have hX : 0 ≤ X := add_nonneg (mul_nonneg (Real.exp_pos _).le hw) (by positivity)
  have hf : D*(Real.exp k*w) ≤ 1/32 := by
    rw [hx, inv_mul_eq_div, ← mul_div_assoc, div_le_iff₀ ht]
    calc
      D*w ≤ D*((1/8)*γ) := mul_le_mul_of_nonneg_left he hd.le
      _ = (1/32)*t := by dsimp only [t]; ring
  have hcD : D*C ≤ 1/32 := hs
  have hcut : D*X ≤ 3/32 := by
    dsimp only [X, Payments.inflation]
    linarith only [hf,hcD,show D*(Real.exp k*w+2*C)=D*(Real.exp k*w)+2*(D*C) by ring]
  have hX' : X ≤ 3/32 := (le_mul_of_one_le_left hX hD).trans hcut
  have hC' : C ≤ 1 := by linarith [le_mul_of_one_le_left hC hD]
  refine ⟨k, hk, hw, hC, hC', ?_, ?_⟩
  · exact hcut.trans (by norm_num)
  change Real.exp (-k)*(Real.exp X-1) ≤ γ
  rw [hy]
  have hg := Real.abs_exp_sub_one_le (x := X)
    (by rw [abs_of_nonneg hX]; linarith)
  rw [abs_of_nonneg hX] at hg
  calc
    t*(Real.exp X-1) ≤ t*(2*X) := mul_le_mul_of_nonneg_left (abs_le.mp hg).2 ht.le
    _ = 8*(D*X)*γ := by dsimp only [t]; ring
    _ ≤ γ := by nlinarith only [mul_le_mul_of_nonneg_right hcut hγ.le,hγ.le]

end YM.Integration.CensusFusionRate
end
