import YM.Integration.WilsonOlderFreshGraphPreimageFee
import YM.Integration.WilsonOlderFreshGraphChildDensity

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointLagPower
open Filter PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open scoped Topology BigOperators Classical

variable {G:Gauge} (R:Run G) (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
variable {j N per:ℕ}
open Pert.Asymptotics
include simple in
private theorem heat : Tendsto R.alloy.B.a.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
  (R.family.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
/-- One date threshold for the entire physical spectrum of each fixed source. -/
def start (d:ℕ):ℕ:=max (WilsonMeasuredLandedCurrency.first R simple)
  (max (WilsonOlderFreshGraphPreimageFee.first R simple slow d)
    (eventually_atTop.mp ((heat R simple).eventually_ge_atTop 8)).choose)

theorem native (d ℓ:ℕ)(cut:j+1<N)(late:start R simple slow d ≤ j):
    let u:=regulatorRun R.family N per (j+1)
    let g:=regulatorRun R.family N per j
    let L:=((R.family.path.levels.S.block (j+1)).val:ℝ)^d
    0≤u^ℓ*L ∧ 0<g ∧ (u^ℓ*L)*g^2≤8:=by
  unfold start at late
  have a:=le_trans (le_max_left ..) late
  have b:=le_trans ((le_max_left ..).trans (le_max_right ..)) late
  have c:=le_trans ((le_max_right ..).trans (le_max_right ..)) late
  have old:=WilsonMeasuredLandedCurrency.native R simple per cut.le a
  have fine:=WilsonMeasuredLandedCurrency.native R simple per cut (a.trans (Nat.le_succ j))
  let g:=regulatorRun R.family N per j
  let u:=regulatorRun R.family N per (j+1)
  have hu:0<u:=fine.2.1
  have h₀:0<g:=old.2.1
  have ht:8 ≤ R.alloy.B.a.clock.hatBeta ((j+1)+1+1):=
    (eventually_atTop.mp ((heat R simple).eventually_ge_atTop 8)).choose_spec _ (c.trans (by omega))
  have uh:u≤1:=by
    have bound:=mul_le_mul_of_nonneg_right ht (sq_nonneg u)
    have endp:R.alloy.B.a.clock.hatBeta ((j+1)+1+1)*u^2≤8:=fine.2.2.1
    nlinarith
  have ul:0≤u^ℓ:=pow_nonneg hu.le _
  have up:u^ℓ≤1:=pow_le_one₀ hu.le uh
  let gain:=((R.family.path.levels.S.block (j+1)).val:ℝ)^d
  have gain₀:0≤gain:=by dsimp [gain];positivity
  have scaled:gain ≤ R.alloy.B.a.clock.hatBeta ((j+1)+1):=by
    have levels:R.family.path.levels=R.alloy.B.a:=rfl
    dsimp only [gain];rw [levels]
    simpa only [Real.rpow_one] using (eventually_atTop.mp
      (WilsonOlderFreshGraphSlowPreimages.block R simple slow d (show 0<(1:ℝ) by norm_num))).choose_spec (j+1) (b.trans (Nat.le_succ j))
  refine ⟨mul_nonneg ul gain₀,h₀,?_⟩
  change u^ℓ*gain*g^2≤8
  exact (mul_le_mul_of_nonneg_right ((mul_le_of_le_one_left gain₀ up).trans scaled) (sq_nonneg _)).trans old.2.2.1

end YM.Integration.WilsonOlderFreshPointLagPower
end
