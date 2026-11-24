import YM.RG01.Slack
import YM.Integration.ActualStartupNormalizedQ

/-! Transfer the actual shifted startup's clock polynomial to the reference
inverse coupling of the same selected step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonStartupClock
open Function Filter Lattice Wilson RG
open PhysicalNext.Repeat.Legato
open scoped Topology
variable {G : Gauge}

theorem growth (R : Run G) (hG : G.Simple) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ m in atTop,
      1+‖R.family.S.scale (m+1)‖ ≤ A * R.family.path.levels.clock.hatBeta m := by
  let L := R.family.path.levels
  let s := G.slopeConstant
  have hs : 0<s := Gauge.slopeConstant_pos hG
  let a := 2+‖L.clock.bar‖
  have ha : 0<a := by dsimp only [a]; positivity
  refine ⟨1+a/s,by positivity,?_⟩
  filter_upwards [RG01.Physical.nextHat hG L,(RG01.Physical.hats hG L).eventually_ge_atTop 1] with m hn hb
  let b := L.clock.hatBeta m
  have hbc : 0 ≤ L.clock.hatBeta (m+1) := zero_le_one.trans (L.fits.delayed _).le
  have he : s*L.S.scale (m+1) = L.clock.hatBeta (m+1)-L.clock.bar := by
    unfold Calendar.hatBeta
    dsimp only [s]
    ring
  have hbound : s*‖L.S.scale (m+1)‖ ≤ b*a := by
    calc _ = ‖s*L.S.scale (m+1)‖ := by rw [norm_mul,Real.norm_of_nonneg hs.le]
         _ = ‖L.clock.hatBeta (m+1)-L.clock.bar‖ := congrArg norm he
         _ ≤ ‖L.clock.hatBeta (m+1)‖+‖L.clock.bar‖ := norm_sub_le ..
         _ ≤ b*a := by
           rw [Real.norm_of_nonneg hbc]
           dsimp only [a,b]
           nlinarith only [hn,hb,mul_nonneg (sub_nonneg.mpr hb) (norm_nonneg L.clock.bar)]
  have ht : ‖L.S.scale (m+1)‖ ≤ (b*a)/s := (le_div_iff₀ hs).2 (by simpa only [mul_comm s ‖L.S.scale (m+1)‖] using hbound)
  change 1+‖L.S.scale (m+1)‖ ≤ (1+a/s)*b
  calc _ ≤ b+(b*a)/s := add_le_add hb ht
       _ = _ := by ring

end YM.Integration.WilsonStartupClock
