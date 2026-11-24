import YM.Integration.WilsonCenteredCaptureClock

/-! The once-divided allowance which occurs in every captured regular
and forced bill is small on the original measured Wilson dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredDividedRoom
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Push.Local Push.PriceCompiler
open scoped Classical Topology
open private YM.Push.Local.width_delay YM.Push.Local.gasRate_le from YM.Push.LOCAL_SPLITTING.Delay
theorem original {G : Gauge} (R : Run G) (simple : G.Simple) :
    ∀ᶠ i : ℕ in atTop,
      LocalComparison.forcedDivisor R.family i ≤ 1 ∧
      hitWidth (R.alloy.B.a.budget i)*R.alloy.B.a.clock.forcedAllowance i /
        LocalComparison.forcedDivisor R.family i ≤ 1 := by
  let A:=R.alloy.B.a
  have rise : Tendsto A.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [rise.eventually YM.Push.Local.width_delay] with i bound
  have live:=allowance_pos A.clock i
  have upper : A.clock.forcedAllowance i≤1 := YM.Push.Local.gasRate_le _
  have div : 0<Real.sqrt (A.clock.forcedAllowance i) := Real.sqrt_pos.mpr live
  change Real.sqrt (A.clock.forcedAllowance i)≤1 ∧ hitWidth (A.budget i)*A.clock.forcedAllowance i /Real.sqrt (A.clock.forcedAllowance i)≤1
  refine ⟨(Real.sqrt_le_sqrt upper).trans_eq Real.sqrt_one,?_⟩
  have cash : A.clock.forcedAllowance i=(Real.sqrt (A.clock.forcedAllowance i))^2 := (Real.sq_sqrt live.le).symm
  calc
    _ = hitWidth (A.budget i)*Real.sqrt (A.clock.forcedAllowance i) := by
      apply (div_eq_iff div.ne').mpr
      rw [mul_assoc,←sq,←cash]
    _ ≤ 1 := bound

end YM.Integration.WilsonCenteredDividedRoom
