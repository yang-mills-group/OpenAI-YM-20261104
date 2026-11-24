import YM.Integration.WilsonOlderFreshSoftSocketStationLedger
import YM.Integration.WilsonIndependentCapturedDates

/-! The independent stopping date is chosen before the planting date and both regulators. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshSoftSocketStationDate
open Function Filter Lattice RG Wilson Real Pert.Asymptotics PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "a_" => R.family.S.a
local notation "σ" => R.family.S.scale
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "g" => regulatorRun R.family

theorem logarithms {x y:ℝ}(xp:0<x)(yp:0<y)(cold:x≤1/2)
    (lower:3/4≤y/x)(upper:y/x≤5/4):
    0≤log x⁻¹ ∧ log y⁻¹≤2*log x⁻¹ ∧ log x⁻¹≤2*log y⁻¹:=by
  have lo:3/4*x≤y:=(le_div_iff₀ xp).mp lower
  have hi:y≤5/4*x:=(div_le_iff₀ xp).mp upper
  have small:x^2≤y:=by nlinarith [mul_nonneg xp.le (show 0≤1/2-x by linarith)]
  have square:y^2≤x:=by
    have h:=pow_le_pow_left₀ yp.le hi 2
    nlinarith [mul_nonneg xp.le (show 0≤1/2-x by linarith)]
  have l:=Real.log_le_log (pow_pos xp 2) small
  have h:=Real.log_le_log (pow_pos yp 2) square
  rw [Real.log_pow] at l h
  simp only [Real.log_inv]
  have neg:=Real.log_nonpos xp.le (show x≤1 by linarith)
  push_cast at l h
  exact ⟨by linarith,by linarith,by linarith⟩

theorem width (simple:G.Simple){v c K e:ℕ}(vc:v≤c)(bound:a_ v/a_ K≤(H v)^e):
    a_ c/a_ K≤(H c)^e:=by
  have step:σ v≤σ c:=(WilsonIndependentCapturedDates.increasing R).monotone vc
  have logs:log (a_ c)≤log (a_ v):=by
    simp only [Schedule.scale,Real.log_inv] at step
    linarith only [step]
  have mesh: a_ c≤a_ v:=(Real.log_le_log_iff (R.family.S.a_pos c) (R.family.S.a_pos v)).mp logs
  have price:=WilsonReflectedOpticalStock.monotone R simple vc
  exact (div_le_div_of_nonneg_right mesh (R.family.S.a_pos K).le).trans
    (bound.trans (pow_le_pow_left₀ (zero_lt_one.trans ((R.family.path.levels).fits.delayed v)).le price e))

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (floor width:ℕ)(loss:ℝ)(positive:0≤loss):
    let n:=2*⌈loss⌉₊
    ∀ᶠc:ℕ in atTop,∃w:ℕ,floor≤w ∧ w≤c ∧
      ∀K N per,c≤K→K≤N→a_ c/a_ K≤(H c)^width→
      let logg:=log (g N per K)⁻¹
      a_ c/a_ w≤exp (-loss*logg) ∧
      loss*logg≤σ c-σ w ∧ σ c-σ w≤8*((n:ℝ)+1)*logg:=by
  let n:=2*⌈loss⌉₊
  obtain ⟨_,_,ready⟩:=WilsonSeparatedPrefixKineticGeometry.corridor R simple width
  filter_upwards [WilsonThermometerUnitFilingWindow.original R simple slow floor n,ready,
    WilsonSeparatedPrefixKineticGeometry.spend R simple 2 0] with c choose paid later
  obtain ⟨w,above,below,stop⟩:=choose
  refine ⟨w,above,below,?_⟩
  intro K N per ck live size
  obtain ⟨xp,_,early,late⟩:=stop N per (ck.trans live)
  have yp:0<g N per K:=ActualRunKernelPackets.regulator_pos R N per K live
  have small:2≤(g N per c)⁻¹:=by simpa only [pow_zero,mul_one] using later N per (ck.trans live)
  have hi:g N per c≤1/2:=by
    have h:2*g N per c≤1:=by simpa [div_eq_mul_inv] using (le_div_iff₀ xp).mp (by simpa using small:2≤1/(g N per c))
    linarith
  have gap:=WilsonSeparatedPrefixKineticAdmitted.admissible (R:=R) (simple:=simple) width c K ck size
  obtain ⟨lo,up⟩:=(paid K N per ck live gap).2 K ck le_rfl
  obtain ⟨nonneg,l,h⟩:=logarithms xp yp hi lo up
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

end YM.Integration.WilsonOlderFreshSoftSocketStationDate
end
