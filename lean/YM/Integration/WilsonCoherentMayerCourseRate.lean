import YM.Integration.WilsonOriginalProjectedCurvatureCourseCash
import YM.Integration.WilsonMovingMentorBentTemperature

/-! The original lower club fidelity in the true fine-temperature currency. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerCourseRate
open Filter RG Push QuadraticLocal ConnectedActivityE6 PhysicalNext.Repeat.Legato
open scoped Topology

theorem purchased {G:Gauge} (R:Run G) (simple:G.Simple) (q:ℕ) {ε:ℝ}(positive:0<ε):
    ∀ᶠ m:ℕ in atTop, ∀ order≥q+3, ∀ N per, m<N →
      (Pressure.betaF G (R.alloy.B.a.clock.hatBeta m) (R.rolls.L (R.alloy.B.a.clock.J (m+1))))^
          Mentor.Tuition.need order (Mentor.Tolerance (R.alloy.B.a.clock.J m))≤
        ε*(Coat.gStep (R.family.path.rep N per (m+1)).beta)^q:=by
  filter_upwards [WilsonMovingMentorBentTemperature.purchased R simple q positive] with m funded
  intro order deep N per hm
  let x:=R.alloy.B.a.clock.hatBeta (m+1)
  have one:1≤x:=(R.alloy.B.a.fits.delayed (m+1)).le
  have tol:Mentor.Tolerance (R.alloy.B.a.clock.J m)≤1:=by
    unfold Mentor.Tolerance
    rw [one_div]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))
  have stage:(q:ℝ)+3≤(order:ℝ):=by exact_mod_cast deep
  have rate:Mentor.Tuition.need order (Mentor.Tolerance (R.alloy.B.a.clock.J m))≤
      LocalTaylorR2.Tail.requested (q+2+1) 1:=by
    unfold Mentor.Tuition.need AllOrder.Catch.graded LocalTaylorR2.Tail.requested
    push_cast
    linarith only [stage,tol]
  rw [←PriceCompiler.beta_eq R.alloy.B.valid m]
  change x^Mentor.Tuition.need order (Mentor.Tolerance (R.alloy.B.a.clock.J m))≤_
  calc
    _ ≤ x^LocalTaylorR2.Tail.requested (q+2+1) 1:=Real.rpow_le_rpow_of_exponent_le one rate
    _ ≤ LocalTaylorR2.Reel.upfront x (q+2) 1:=by
      change _ ≤ 2*(x^LocalTaylorR2.Tail.requested (q+2+1) 1)
      linarith only [Real.rpow_nonneg (zero_le_one.trans one) (LocalTaylorR2.Tail.requested (q+2+1) 1)]
    _ ≤ _:=funded (m+1) (Nat.le_succ m) N per hm _ le_rfl 1 le_rfl
end YM.Integration.WilsonCoherentMayerCourseRate
