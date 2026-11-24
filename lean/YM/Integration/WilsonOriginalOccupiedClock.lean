import YM.Integration.WilsonOriginalOccupiedCorridor
import YM.Integration.WilsonThermometerMixedCollarSubpower

/-! Restoration of every original radius on its own occupied subset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedClock
open Filter Finset Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Advent PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato ActualRunKernelPackets Pressure ConnectedActivityE6 Pert.Asymptotics
open WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open MergeProof.Accent
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "H" i:max=>R.family.path.levels.clock.hatBeta i
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
  unfold factor WilsonThermometerMixedCorridor.factor WilsonThermometerMixedCorridor.rent
  refine max_le (Real.one_le_exp (pow_nonneg (z1.trans step) _)) ((min_le_left ..).trans ?_)
  change Real.exp ((scale (H (j+1)))^3) ≤ _
  exact Real.exp_le_exp.mpr (pow_le_pow_left₀ z1 step _)


variable {V:Type} [DecidableEq V] {marks:Census V}

private theorem step {z:V → ℝ}(k:ℝ)(hk:0<k)(s:marks.Mode):
    Poly.toll z s=k^s.val.card*Poly.toll (Stoop.radius z k) s:=by
  change (∏v∈s.val,z v)=k^s.val.card*∏v∈s.val,(z v/k)
  rw [prod_div_distrib];simp only [prod_const]
  field_simp

include simple in
theorem restored {b t f:ℕ}(bt:b ≤ t)(tf:t ≤ f+1)(w:V → ℝ)(wp:∀v,0<w v)(s:marks.Mode):
    Poly.toll w s ≤ Real.exp (s.val.card*(t-b:ℕ)*(scale (H (f+1)))^3)*
      Poly.toll (wallet R w bt) s:=by
  let z:=scale (H (f+1))
  let n:=s.val.card
  refine Nat.decreasingInduction (motive:=fun j jt=>Poly.toll w s ≤
    Real.exp (n*(t-j:ℕ)*z^3)*Poly.toll (wallet R w jt) s) ?_ ?_ bt
  · intro j jt ih
    have hp:=WilsonOriginalOccupiedCorridor.positive R w wp jt
    have fj:0<factor R j:=zero_lt_one.trans_le (le_max_left ..)
    have tag:(factor R j)^n ≤ Real.exp (n*z^3):=by
      calc _ ≤ (Real.exp (z^3))^n:=pow_le_pow_left₀ fj.le (one R simple ((show j+1≤t from jt).trans tf)) _
           _ = _:=by rw [←Real.exp_nat_mul]
    rw [show wallet R w jt.le=Stoop.radius (wallet R w jt) (factor R j) from Nat.decreasingInduction_succ_left ..,
      show t-j=t-(j+1)+1 by omega,Nat.cast_add,Nat.cast_one,
      show (n:ℝ)*((t-(j+1):ℕ)+1:ℝ)*z^3=(n*(t-(j+1):ℕ)*z^3)+(n*z^3) by ring,
      Real.exp_add,mul_assoc]
    refine ih.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    rw [step (z:=wallet R w jt) (factor R j) fj s]
    exact mul_le_mul_of_nonneg_right tag (Poly.worth (fun v=>div_pos (hp v) fj) s).le
  · rw [show wallet R w (le_refl t)=w from Nat.decreasingInduction_self ..];simp

end YM.Integration.WilsonOriginalOccupiedClock
