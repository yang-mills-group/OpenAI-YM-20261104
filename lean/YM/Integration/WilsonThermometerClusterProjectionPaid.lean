import YM.Integration.WilsonThermometerClusterProjectionBudget
import YM.RG01.Slack

/-! A fixed polynomial in the true inverse coupling pays the scalar filing on the original gauge door. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerClusterProjectionPaid
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus ConnectedActivityE6.Blaze Blaze.March
open RG.Supply Precision Tree ThroughLaunch Push.PriceCompiler Input Next.Scheduling
open WilsonReportLampForecast WilsonReportRetainedAnchor
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}
private theorem angular (A:Levels G) (m:ℕ):
    reprice (A.budget m) (A.budget m).B=(1+2*(radiusB (A.clock.hatBeta m):ℝ))^(2*((A.params m).power*(A.params m).order)):=by
  let b:=radiusB (A.clock.hatBeta m)
  change ((1+((b*(4*b+2)+2*b:ℕ):ℝ))^(A.params m).power)^(A.params m).order=_
  push_cast
  rw [show 1+((b:ℝ)*(4*b+2)+2*b)=(1+2*(b:ℝ))^2 by ring,←pow_mul,←pow_mul]

private theorem voltage (v:Stage) (x:ℝ):
    2*|Graces.host G v 0| *|Mercury.volt x v.order v.power| ≤
      WilsonThermometerClusterProjectionBudget.charge (G:=G) v*
        (1+2*(radiusB x:ℝ))^(2*(v.power*v.order)):=by
  let n:=v.power*v.order
  have one:1≤1+2*(radiusB x:ℝ):=le_add_of_nonneg_right (by positivity)
  have h:0≤WilsonThermometerClusterProjectionBudget.charge (G:=G) v:=by
    unfold WilsonThermometerClusterProjectionBudget.charge;positivity
  calc 2*|Graces.host G v 0| *|Mercury.volt x v.order v.power| =
        WilsonThermometerClusterProjectionBudget.charge (G:=G) v*(1+2*(radiusB x:ℝ))^n := by
          unfold WilsonThermometerClusterProjectionBudget.charge Mercury.volt shiftG
          rw [abs_mul,abs_pow,abs_of_nonneg (show 0≤4*(2*(radiusB x:ℝ)+1) by positivity),mul_pow]
          rw [add_comm (2*(radiusB x:ℝ)) 1]
          ring
       _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one (by dsimp [n]; omega)) h

variable (R:Run G)
local notation "A" => R.alloy.B.a
local notation "J" => (A).clock.J
local notation "β" => (A).clock.hatBeta

theorem original (simple:G.Simple) (bank:WilsonThermometerClusterProjectionBudget.Ready (A))
    (wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ m:ℕ in atTop, WilsonThermometerClusterProjectionFee.price R m 0 ≤ (β m)^4 := by
  filter_upwards [bank,wage 0,RG01.Physical.nextHat simple (A),
    Many.theta_up (C:=R.family) 3 simple] with m fixed radial next hot
  rw [angular,params_eq R.alloy.B.valid m] at radial
  simp only [WilsonReportLampForecast.part,Nat.cast_zero,zero_add,div_one,Real.rpow_one] at radial
  rw [params_eq R.alloy.B.valid m] at fixed
  let P:=R.metals.p.profile (J m)
  let Q:=R.kit.target (J (m+1)) (J m)
  let L:=R.rolls.L (J (m+1))
  let x:=β m
  have hx:3≤x:=hot
  have host:=voltage (G:=G) P x
  have pot: 2*|Graces.host G P 0| *|Mercury.volt x P.order P.power|≤x^2 := by
    rw [pow_two]
    exact host.trans (mul_le_mul fixed radial (by positivity) (by linarith))
  have upper:β (m+1)=Pressure.betaF G x L:=by
    rw [Extra.Iteration.block_beta,Extra.Iteration.block_eq R.alloy.B.valid]
  have base:1≤β (m+1):=(A).fits.delayed (m+1)|>.le
  have inv:0≤(Q.goal L x)⁻¹ ∧ (Q.goal L x)⁻¹≤2*x:=by
    rw [Target.goal,←upper,←Real.rpow_neg (by linarith:0≤ β (m+1))]
    refine ⟨Real.rpow_nonneg (by linarith) _,?_⟩
    exact (Real.rpow_le_rpow_of_exponent_le base (show -Q.rate ≤ 1 by linarith only [Q.start])).trans
      (by simpa only [Real.rpow_one] using next)
  have lprice:Doors.rate L≤1:=by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast L.property) (by norm_num)
  change (Graces.coinFee G P 0 L + |2*(L.val:ℝ)^0 * (Mercury.volt x P.order P.power*(Q.goal L x)⁻¹)|)*
    Graces.host G P 0 ≤ x^4
  by_cases zero:Graces.host G P 0=0
  · rw [zero,mul_zero]; positivity
  · rw [pow_zero,mul_one,add_mul,Graces.coinFee,div_mul_cancel₀ _ zero,
      abs_mul,abs_mul,abs_of_nonneg (show (0:ℝ)≤2 by norm_num),abs_of_nonneg inv.1]
    calc Doors.rate L+ 2*(|Mercury.volt x P.order P.power| *(Q.goal L x)⁻¹)*Graces.host G P 0
        ≤ 1+2*(|Mercury.volt x P.order P.power| *(Q.goal L x)⁻¹)*|Graces.host G P 0| :=
          add_le_add lprice (mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) inv.1)))
       _=1+(2*|Graces.host G P 0| *|Mercury.volt x P.order P.power|)*(Q.goal L x)⁻¹:=by ring
       _≤1+x^2*(2*x):=add_le_add_right (mul_le_mul pot inv.2 inv.1 (sq_nonneg _)) _
       _≤x^4:=by nlinarith [sq_nonneg (x-1),sq_nonneg (x*x-1),mul_nonneg (show 0≤x-3 by linarith) (show 0≤x^3 by positivity)]

end YM.Integration.WilsonThermometerClusterProjectionPaid
end
