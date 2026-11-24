import YM.Integration.WilsonOlderFreshSoftSocketStationScale

/-! The physical extent from the station to the planting cell, including the station's own displacement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationUnits
open Function Filter Lattice Wilson RG Next.Rank Pert.Asymptotics
open PhysicalNext.Repeat.Legato
open WilsonOlderFreshSoftSocketStationScale
open scoped Classical Topology

variable {G:Gauge}(R:Run G)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a_" => R.family.S.a
local notation "road" => R.family.path.levels

theorem original (simple:G.Simple)(width:ℕ){η:ℝ}(pos:0<η):∀ᶠj:ℕ in atTop,
    ∀(b:ℝ),b≤Perch.y (β j)→∀(v K N per:ℕ),v≤j→j≤K→K≤N→8≤β K→a_ v/a_ K≤(β v)^width→
    let s:=Real.log (regulatorRun R.family N per K)⁻¹
    Real.log (a_ K/a_ j)⁻¹≤(3*(width:ℝ))*s ∧
    ∀d:ℕ,(Station.gap road b j/a_ K)^d≤Real.exp ((d:ℝ)*(3*((width:ℝ)+η))*s):=by
  filter_upwards [extent R simple pos] with j raw
  intro b cap v K N per upper lower live warm band s
  have jKβ:=WilsonStartup.Timing.hat_mono road (Gauge.slopeConstant_pos simple).le lower
  have vKβ:=WilsonStartup.Timing.hat_mono road (Gauge.slopeConstant_pos simple).le (upper.trans lower)
  have hv0:0≤β v:=zero_le_one.trans ((road).fits.delayed v).le
  have hj0:0≤β j:=zero_le_one.trans ((road).fits.delayed j).le
  have mag:Station.mag road b j≤Real.exp ((3*η)*s):=
    (raw b cap).trans ((Real.rpow_le_rpow hj0 jKβ pos.le).trans (heated R N per K live warm η pos.le))
  have step:a_ j/a_ K≤Real.exp ((3*(width:ℝ))*s):=by
    apply (div_le_div_of_nonneg_right (R.family.S.strictAnti.antitone upper) (R.family.S.a_pos K).le).trans
    apply band.trans
    apply (pow_le_pow_left₀ hv0 vKβ width).trans
    simpa only [Real.rpow_natCast] using heated R N per K live warm (width:ℝ) (Nat.cast_nonneg _)
  constructor
  · rw [inv_div]
    exact (Real.log_le_log (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)) step).trans_eq (Real.log_exp _)
  · intro d
    have spot:Station.gap road b j/a_ K≤Real.exp ((3*((width:ℝ)+η))*s):=by
      calc
        _=a_ j/a_ K*Station.mag road b j:=by unfold Station.gap;ring
        _≤Real.exp ((3*(width:ℝ))*s)*Real.exp ((3*η)*s):=
          mul_le_mul step mag (Station.mag_pos ..).le (Real.exp_pos _).le
        _=_:=by rw [←Real.exp_add];congr 1;ring
    apply (pow_le_pow_left₀ (div_nonneg (Station.gap_pos ..).le (R.family.S.a_pos _).le) spot d).trans_eq
    rw [←Real.exp_nat_mul]
    congr 1
    ring

end YM.Integration.WilsonOlderFreshSoftSocketStationUnits
end
