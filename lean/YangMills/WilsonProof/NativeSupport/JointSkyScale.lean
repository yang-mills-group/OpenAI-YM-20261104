import YangMills.WilsonProof.NativeSupport.JointOriginalTempo
import YangMills.WilsonProof.NativeSupport.JointForcedClock
import YM.FullVolume.Fares.Dusk

/-! The support-exponent tariff for a fresh source is already purchased
by the original selected Sky at the next finer global schedule edge.
This includes the ultraviolet planting plane. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Filter Lattice RG Wilson PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Push.PriceCompiler Extra.Iteration PhysicalNext.JointLoad.Heir
open scoped Classical BigOperators
variable {G:Gauge} {R:Run G} {T:Campaign R} {Θ:Luna.Tableau T.width 300} {v:ℕ → ℕ → ℝ}
local notation "A" => R.alloy.B.a

theorem sky_block_fee (sky:Campaign.Sky R T Θ v) (i:ℕ) :
    Real.exp ((R.alloy.B.a.budget i).supportExponent+2) ≤ ((R.alloy.B.a.S.block i).val:ℝ) := by
  let a:=(R.alloy.B.a.budget i).supportExponent+2
  let r:=R.kit.span ((A).clock.J (i+1)) ((A).clock.J i)
  have nonnegative:0 ≤ a := by dsimp [a]; linarith only [sky.supports i]
  have tollOne : (1:ℝ) ≤ Planned.AtomRegular.toll r := by
    exact_mod_cast (show 1 ≤ Planned.AtomRegular.toll r by
      change 0 < ((r+6)+(r+6)+1)^4; positivity)
  have small:a ≤ Release.base a r := by
    unfold Release.base
    simpa only [mul_one] using mul_le_mul_of_nonneg_left tollOne nonnegative
  have paid:=sky.fee _ _ (step_paid (A) i)
  rw [show (R.metals.p.profile ((A).clock.J i)).supportExponent=((A).budget i).supportExponent by
    change _=((A).params i).supportExponent
    rw [params_eq R.alloy.B.valid i]] at paid
  rw [Extra.Iteration.block_eq R.alloy.B.valid i]
  exact (Real.exp_le_exp.mpr small).trans paid

theorem sky_stencil (sky:Campaign.Sky R T Θ v) (simple:G.Simple)
    (slow:∀ m,((R.alloy.B.a.S.block m).val:ℝ) ≤ Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta m)))
    {i N:ℕ} (upto:i ≤ N) (s:ℕ) :
    Real.exp (((R.alloy.B.a.budget i).supportExponent+1)*(s:ℝ)) ≤ (⌈(A).clock.hatBeta N⌉₊:ℝ)^s ∧
    (1/((⌈(A).clock.hatBeta N⌉₊:ℝ)^2)) ≤ (R.alloy.B.a.clock.hatBeta i)⁻¹^2 := by
  let a:=R.alloy.B.a
  have scaleInc:Monotone a.S.scale := monotone_nat_of_le_succ fun j=>by
    rw [Schedule.scale_succ]
    exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (a.S.block j).property))
  have heat:a.clock.hatBeta i ≤ a.clock.hatBeta N := by
    change a.clock.bar+G.slopeConstant*a.S.scale i ≤ a.clock.bar+G.slopeConstant*a.S.scale N
    gcongr
    · exact (Gauge.slopeConstant_pos simple).le
    · exact scaleInc upto
  have bi:0 < a.clock.hatBeta i := zero_lt_one.trans (a.fits.delayed i)
  have top:=Nat.le_ceil (a.clock.hatBeta N)
  have plus:0 < 2+Real.log (a.clock.hatBeta i) :=
    add_pos_of_pos_of_nonneg two_pos (Real.log_nonneg (a.fits.delayed i).le)
  have logcap:Real.log (2+Real.log (a.clock.hatBeta i)) ≤ a.clock.hatBeta i := by
    linarith only [Real.log_le_sub_one_of_pos plus,Real.log_le_sub_one_of_pos bi]
  have fee:=sky_block_fee sky i
  constructor
  · rw [Real.exp_mul,Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.exp_pos _).le
      (((Real.exp_le_exp.mpr (by linarith : (a.budget i).supportExponent+1 ≤ (a.budget i).supportExponent+2)).trans fee).trans
        ((slow i).trans (logcap.trans (heat.trans top)))) s
  · rw [one_div,inv_pow]
    exact inv_anti₀ (sq_pos_of_pos bi) (pow_le_pow_left₀ bi.le (heat.trans top) 2)

end YM.Integration.InletSusceptibility.Packet
