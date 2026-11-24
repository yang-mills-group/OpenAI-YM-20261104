import YM.Integration.WilsonOlderFreshSoftSocketStationDate

/-! One independent stop from the relative capture alone, before the later optical corridor and both regulators. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshSoftSocketStationNatural
open Filter Function RG Wilson Real Pert.Asymptotics PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "a_" => R.family.S.a
local notation "σ" => R.family.S.scale
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "g" => regulatorRun R.family

def Stopped (n c w:ℕ):Prop:=
  ∀N per,c≤N→let z:=log (g N per c)⁻¹
    n*z≤σ c-σ w ∧ σ c-σ w≤4*((n:ℝ)+1)*z

def date (loss:ℝ)(c:ℕ):ℕ:=
  Nat.findGreatest (Stopped R (2*⌈loss⌉₊) c) c

theorem earlier (loss:ℝ)(c:ℕ):date R loss c≤c:=Nat.findGreatest_le _

theorem elected (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(loss:ℝ):
    Tendsto (date R loss) atTop atTop ∧
    ∀ᶠc:ℕ in atTop,Stopped R (2*⌈loss⌉₊) c (date R loss c):=by
  have calendar(gate:ℕ):∀ᶠ c:ℕ in atTop,∃w,gate≤w ∧ w≤c ∧ Stopped R (2*⌈loss⌉₊) c w:=by
    filter_upwards [WilsonThermometerUnitFilingWindow.original R simple slow gate (2*⌈loss⌉₊)] with c quote
    obtain ⟨w,late,below,heard⟩:=quote
    exact ⟨w,late,below,fun N per live=>(heard N per live).2.2⟩
  constructor
  · apply tendsto_atTop.2
    intro gate
    filter_upwards [calendar gate] with c quote
    obtain ⟨w,late,below,filed⟩:=quote
    exact late.trans (Nat.le_findGreatest (P:=Stopped R (2*⌈loss⌉₊) c) below filed)
  · filter_upwards [calendar 0] with c quote
    obtain ⟨w,_,below,filed⟩:=quote
    exact Nat.findGreatest_spec (P:=Stopped R (2*⌈loss⌉₊) c) below filed

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(loss:ℝ)(positive:0≤loss)(width:ℕ):
    ∀ᶠc:ℕ in atTop,∀K N per,c≤K→K≤N→a_ c/a_ K≤(H c)^width→
      let w:=date R loss c
      let logg:=log (g N per K)⁻¹
      a_ c/a_ w≤exp (-loss*logg) ∧ loss*logg≤σ c-σ w ∧
        σ c-σ w≤8*((2*⌈loss⌉₊:ℕ)+1:ℝ)*logg:=by
  let n:=2*⌈loss⌉₊
  obtain ⟨_,_,ready⟩:=WilsonSeparatedPrefixKineticGeometry.corridor R simple width
  filter_upwards [(elected R simple slow loss).2,ready,
    WilsonSeparatedPrefixKineticGeometry.spend R simple 2 0] with c paidStop paid later K N per ck live size
  let w:=date R loss c
  obtain ⟨early,late⟩:=paidStop N per (ck.trans live)
  change (n:ℝ)*log (g N per c)⁻¹≤σ c-σ w at early
  change σ c-σ w≤4*((n:ℝ)+1)*log (g N per c)⁻¹ at late
  have xp:0<g N per c:=ActualRunKernelPackets.regulator_pos R N per c (ck.trans live)
  have yp:0<g N per K:=ActualRunKernelPackets.regulator_pos R N per K live
  have small:2≤(g N per c)⁻¹:=by simpa only [pow_zero,mul_one] using later N per (ck.trans live)
  have hi:g N per c≤1/2:=by
    have h:2*g N per c≤1:=by simpa [div_eq_mul_inv] using (le_div_iff₀ xp).mp (by simpa using small:2≤1/(g N per c))
    linarith
  have gap:=WilsonSeparatedPrefixKineticAdmitted.admissible (R:=R) (simple:=simple) width c K ck size
  obtain ⟨lo,up⟩:=(paid K N per ck live gap).2 K ck le_rfl
  obtain ⟨nonneg,l,h⟩:=WilsonOlderFreshSoftSocketStationDate.logarithms xp yp hi lo up
  have pc:loss≤(⌈loss⌉₊:ℝ):=Nat.le_ceil loss
  have first:loss*log (g N per K)⁻¹≤σ c-σ w:=by
    have a:=mul_le_mul_of_nonneg_left l positive
    have b:=mul_le_mul_of_nonneg_right pc nonneg
    dsimp [n] at early;push_cast at early
    linarith only [early,a,b]
  have last:σ c-σ w≤8*((n:ℝ)+1)*log (g N per K)⁻¹:=by
    have h':=mul_le_mul_of_nonneg_left h (show 0≤4*((n:ℝ)+1) by positivity)
    linarith only [h',late]
  refine ⟨?_,first,last⟩
  apply (Real.log_le_log_iff (div_pos (R.family.S.a_pos c) (R.family.S.a_pos w)) (Real.exp_pos _)).mp
  rw [WilsonIndependentCapturedDates.mesh,Real.log_exp]
  linarith only [first]

end YM.Integration.WilsonOlderFreshSoftSocketStationNatural
end
