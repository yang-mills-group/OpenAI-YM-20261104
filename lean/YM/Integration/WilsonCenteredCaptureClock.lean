import YM.Integration.WilsonMovingMentorConcourseRows
import YM.Push.LOCAL_SPLITTING.Delay

/-! The forced owner budget on the original Wilson calendar has enough
room for the additional copies at the capture, before either regulator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCaptureClock
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Push.Local Push.PriceCompiler
open scoped Classical Topology
open private YM.Push.Local.width_delay YM.Push.Local.gasRate_le from YM.Push.LOCAL_SPLITTING.Delay

theorem original {G : Gauge} (R : Run G) (simple : G.Simple) :
    ∀ᶠ i : ℕ in atTop,
      0 < LocalComparison.forcedDivisor R.family i ∧
      0 ≤ R.alloy.B.a.clock.forcedAllowance i ∧
      hitWidth (R.alloy.B.a.budget i)*R.alloy.B.a.clock.forcedAllowance i≤1 := by
  let A:=R.alloy.B.a
  have rise : Tendsto A.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [rise.eventually YM.Push.Local.width_delay] with i bound
  have live:=allowance_pos A.clock i
  have upper : A.clock.forcedAllowance i≤1 := YM.Push.Local.gasRate_le _
  have small : A.clock.forcedAllowance i≤Real.sqrt (A.clock.forcedAllowance i) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [mul_nonneg live.le (sub_nonneg.mpr upper)])
  refine ⟨Real.sqrt_pos.mpr live,live.le,?_⟩
  exact (mul_le_mul_of_nonneg_left small (by unfold hitWidth; positivity : 0≤hitWidth (A.budget i))).trans bound

def first {G : Gauge} (R : Run G) (hg : G.Simple) : ℕ := (eventually_atTop.mp (original R hg)).choose

end YM.Integration.WilsonCenteredCaptureClock
