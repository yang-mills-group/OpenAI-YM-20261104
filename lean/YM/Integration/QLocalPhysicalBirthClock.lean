import YM.Integration.ActualRunStrongIntake
import YM.RG01.Slack
import YM.Push.LOCAL_SPLITTING.Funding

/-! The physical clock itself pays the full original compulsory cluster
forest width at every sufficiently late level. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalBirthClock
open Filter Lattice Wilson RG PhysicalNext.Repeat.Legato
open scoped Topology Classical

variable {G : Gauge}

theorem width (A : Levels G) (m : ℕ) : Push.Local.hitWidth (A.budget m) ≤
    5^4 * (A.clock.hatBeta m)^8 := by
  let x := A.clock.hatBeta m
  have hx : 1 < x := A.fits.delayed m
  have hC : (⌈(Real.log x)^2⌉₊ : ℝ) ≤ 2*x^2 := by
    have := Real.log_pos hx
    nlinarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans hx),Nat.ceil_lt_add_one (sq_nonneg (Real.log x))]
  change (((⌈(Real.log x)^2⌉₊+⌈(Real.log x)^2⌉₊+1)^4 : ℕ) : ℝ) ≤ 5^4*x^8
  push_cast
  exact (pow_le_pow_left₀ (by positivity) (by nlinarith : _+_+1 ≤ 5*x^2) 4).trans_eq (by ring)

theorem late_forcing (hG : G.Simple) (A : Levels G) : Tendsto (fun m =>
    Push.Local.hitWidth (A.budget m) * A.clock.forcedAllowance m) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (5^4 : ℝ))).mul (RG01.Physical.shrink hG A 8)
  rw [mul_zero] at h
  apply squeeze_zero (fun m => mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)) _ h
  intro m
  calc Push.Local.hitWidth (A.budget m) * A.clock.forcedAllowance m ≤
      (5^4*(A.clock.hatBeta m)^8)*A.clock.forcedAllowance m :=
        mul_le_mul_of_nonneg_right (width A m) (Real.exp_nonneg _)
    _ = _ := by ring

def reserve (R : Run G) : ℝ := min 4 (ActualRunStrongIntake.inputSupport R)

theorem positive (R : Run G) : 0 < reserve R := lt_min (by norm_num)
  ((ActualRunStrongIntake.support_reserves R).1.trans (ActualRunStrongIntake.support_reserves R).2)

theorem permitted (R : Run G) (L : ℕ) :
    max 0 ((R.family.path.levels.budget L).supportExponent-4) + reserve R ≤
      (R.family.path.levels.budget L).supportExponent := by
  have hr : reserve R ≤ 4 := min_le_left _ _
  have hs : reserve R ≤ (R.family.path.levels.budget L).supportExponent :=
    (min_le_right _ _).trans (ActualRunStrongIntake.supports_le R L).1
  rcases le_total 0 ((R.family.path.levels.budget L).supportExponent-4) with hp | hp
  · rw [max_eq_right hp]
    linarith
  · simpa only [max_eq_left hp,zero_add] using hs

/-- At the actual normative price, every late level retains at least half
of one fixed positive exponential-support reserve for nonzero marked input. -/
theorem purchased (R : Run G) (hG : G.Simple) : ∀ᶠ L in atTop,
    Push.Local.hitWidth (R.family.path.levels.budget L) *
      R.family.path.levels.clock.forcedAllowance L ≤ reserve R / 2 := by
  exact (late_forcing hG R.family.path.levels).eventually_le_const (half_pos (positive R))

end YM.Integration.QLocalPhysicalBirthClock
end
