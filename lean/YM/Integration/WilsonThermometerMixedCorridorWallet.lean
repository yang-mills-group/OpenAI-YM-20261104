import YM.Integration.WilsonThermometerMixedCollarSubpower
import YM.Integration.WilsonThermometerMixedCorridor

/- The one coupon on the real end temperature restores the authentic corridor
   wallet. Each of the three marker radii is recovered on its own occupied face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedCorridorWallet
open Filter Finset Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Advent PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato ActualRunKernelPackets Pressure ConnectedActivityE6 Pert.Asymptotics
open WilsonGeometricSignedCapture WilsonThermometerMixedCorridor WilsonThermometerMixedCollarSubpower
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "H" i:max=>R.family.path.levels.clock.hatBeta i
local notation "J"=>Stock.census (Fin 3)

include simple in
private theorem one {j f:ℕ}(jf:j+1≤f+1):
    factor R j ≤ Real.exp ((scale (H (f+1)))^3):=by
  have hp:1<H (j+1):=R.family.path.levels.fits.delayed _
  have h0:0<H (j+1):=zero_lt_one.trans hp
  have h1:=WilsonStartup.Timing.hat_mono R.family.path.levels (G.slopeConstant_pos simple).le jf
  have log1:=Real.log_le_log h0 h1
  have log2:=Real.log_le_log (Real.log_pos hp) log1
  have z1:0 ≤ scale (H (j+1)):=by dsimp [scale];linarith only [le_max_left 0 (Real.log (Real.log (H (j+1))))]
  have step:scale (H (j+1)) ≤ scale (H (f+1)):=by
    unfold scale;gcongr
  unfold factor rent
  refine max_le (Real.one_le_exp (pow_nonneg (z1.trans step) _)) ((min_le_left ..).trans ?_)
  change Real.exp ((scale (H (j+1)))^3) ≤ _
  exact Real.exp_le_exp.mpr (pow_le_pow_left₀ z1 step _)

include simple in
theorem carried {b t f:ℕ}(bt:b≤t)(tf:t≤f+1)(c:(J).Mode→ℂ)(w:Fin 3→ℝ)(wp:∀j,0<w j):
    weightBill c (wallet R w bt) ≤ Real.exp (3*(t-b:ℕ)*(scale (H (f+1)))^3)*weightBill c w:=by
  let z:=scale (H (f+1))
  have base:0≤weightBill c w:=by unfold weightBill;exact sum_nonneg fun s _=>div_nonneg (norm_nonneg _) (Poly.worth wp s).le
  refine Nat.decreasingInduction (motive:=fun j jt=>weightBill c (wallet R w jt)≤Real.exp (3*(t-j:ℕ)*z^3)*weightBill c w) ?_ ?_ bt
  · intro j jt ih
    have hp:=WilsonThermometerMixedCorridor.positive R w wp jt
    have reduction:=WilsonThermometerMixedWages.shrink c (wallet R w jt) hp (le_max_left 1 (rent R j))
    have tag: (factor R j)^3 ≤ Real.exp (3*z^3):=by
      calc (factor R j)^3 ≤ (Real.exp (z^3))^3:=pow_le_pow_left₀ (zero_le_one.trans (le_max_left ..)) (one R simple ((show j+1≤t from jt).trans tf)) _
           _ = Real.exp (3*z^3):=by rw [←Real.exp_nat_mul];norm_num
    rw [show wallet R w jt.le=Stoop.radius (wallet R w jt) (factor R j) from Nat.decreasingInduction_succ_left ..,
      show t-j=t-(j+1)+1 by omega,Nat.cast_add,Nat.cast_one,
      show 3*((t-(j+1):ℕ)+1:ℝ)*z^3=3*z^3+(3*(t-(j+1):ℕ)*z^3) by ring,Real.exp_add,mul_assoc]
    have costNonneg : 0 ≤ weightBill c (wallet R w jt) := by
      unfold weightBill
      exact sum_nonneg fun s _=>div_nonneg (norm_nonneg _) (Poly.worth hp s).le
    exact reduction.trans (mul_le_mul tag ih costNonneg (Real.exp_pos _).le)
  · rw [show wallet R w (le_refl t)=w from Nat.decreasingInduction_self ..];simp

include simple in
theorem original (C:ℝ)(cp:0≤C)(d:ℕ):∀ᶠ f:ℕ in atTop,
    ∀N,f+1≤N→∀per b t,∀bt:b≤t,t≤f+1→ (t-b:ℕ)≤C*(scale (H (f+1)))^d →
    ∀c:(J).Mode→ℂ,∀w:Fin 3→ℝ,(∀j,0<w j)→
    regulatorRun R.family N per (f+1)*weightBill c (wallet R w bt)≤weightBill c w:=by
  filter_upwards [WilsonThermometerMixedCollarSubpower.original R simple C cp d] with f tariff N live per b t bt tf span c w wp
  have gp:=ActualRunKernelPackets.regulator_pos R N per (f+1) live
  have price:=tariff N live per ((t-b:ℕ):ℝ) span
  have initialCash : 0 ≤ weightBill c w := by
    unfold weightBill
    exact sum_nonneg fun s _=>div_nonneg (norm_nonneg _) (Poly.worth wp s).le
  have carriedBill:=carried R simple bt tf c w wp
  calc
    _ ≤ _:=mul_le_mul_of_nonneg_left carriedBill gp.le
    _ = (regulatorRun R.family N per (f+1)*Real.exp (3*(t-b:ℕ)*(scale (H (f+1)))^3))*weightBill c w:=by ring
    _ ≤ 1*weightBill c w:=mul_le_mul_of_nonneg_right price initialCash
    _ = _:=one_mul _
end YM.Integration.WilsonThermometerMixedCorridorWallet
end
