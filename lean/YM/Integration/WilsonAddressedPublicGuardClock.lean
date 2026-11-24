import YM.Integration.WilsonAddressedPhysicalCollar
import YM.Integration.WilsonAddressedPublicOpticalFare

/-! The optical engineering window and its original measured regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicGuardClock
open OPE Trace.Pilot Filter Real PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address OPE.Therm
open WilsonInvariantActionPosition Wilson RG Source Extra.Histories QuadraticLocal.Advent
open scoped Topology
variable {G:Gauge} (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
local notation "a_" => R.family.S.a
local notation "H_" => R.family.path.levels.clock.hatBeta

def ceiling (G:Gauge)(t:ℕ)(δ:ℝ):ℝ:=1+G.slopeConstant*((t:ℝ)+δ)

include simple slow in
theorem thermal (t:ℕ){δ:ℝ}(pos:0<δ):
    ∀ᶠ f:ℕ in atTop,H_ (berth R t f) ≤ ceiling G t δ*H_ f:=by
  have slope:=Gauge.slopeConstant_pos simple
  filter_upwards [WilsonAddressedCollarWindow.original R simple slow t pos] with f tab
  let K:=berth R t f
  have hp:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  have fk:=div_pos (R.family.S.a_pos f) (R.family.S.a_pos K)
  have purchase:a_ f/a_ K≤H_ f^((t:ℝ)+δ):=by rw [Real.rpow_add hp,Real.rpow_natCast];exact tab.2.2
  have before:Real.log (a_ f/a_ K)≤((t:ℝ)+δ)*H_ f:=by
    calc
      _ ≤ Real.log ((H_ f)^((t:ℝ)+δ)):=Real.log_le_log fk purchase
      _ = ((t:ℝ)+δ)*Real.log (H_ f):=Real.log_rpow hp _
      _ ≤ _:=mul_le_mul_of_nonneg_left (Real.log_le_self hp.le) (add_nonneg (Nat.cast_nonneg _) pos.le)
  have duration:R.family.S.scale K-R.family.S.scale f=Real.log (a_ f/a_ K):=by
    rw [Schedule.scale,Schedule.scale,Real.log_inv,Real.log_inv,
      Real.log_div (R.family.S.a_pos _).ne' (R.family.S.a_pos _).ne']
    ring
  have realClock:H_ K-H_ f=G.slopeConstant*Real.log (a_ f/a_ K):=by
    rw [←duration]
    change (_+G.slopeConstant*_)-(_+G.slopeConstant*_) = _
    ring
  have debit:=mul_le_mul_of_nonneg_left before slope.le
  change H_ K≤(1+G.slopeConstant*((t:ℝ)+δ))*H_ f
  linarith only [realClock,debit]

include slow in
theorem physical (v t:ℕ)(native:0<v){δ:ℝ}(pos:0<δ):∀ᶠ r:ℝ in trail,
    let m:=WilsonMeasuredWindow.stop R.family.path.levels simple v r
    let f:=berth R t m
    r/a_ f ≤ (H_ f)^((t:ℝ)+2*δ):=by
  filter_upwards [WilsonAddressedPhysicalCollar.original R simple slow v t native δ pos] with r tab
  dsimp only
  let m:=WilsonMeasuredWindow.stop R.family.path.levels simple v r
  let f:=berth R t m
  have hp:=zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have cost:(H_ m)^t*((H_ m)^δ)^2=(H_ m)^((t:ℝ)+2*δ):=by
    rw [Real.rpow_add hp,Real.rpow_natCast,mul_comm (2:ℝ) δ,Real.rpow_mul hp.le,Real.rpow_two]
  exact (tab.2.2.2.2.trans_eq cost).trans (Real.rpow_le_rpow hp.le
    (PaceR.clock_mono R simple (le_of_lt tab.1)) (by positivity))

end YM.Integration.WilsonAddressedPublicGuardClock
end
