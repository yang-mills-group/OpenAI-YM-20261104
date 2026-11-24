import YM.Integration.WilsonReportingRegulatedFactory
import YM.Integration.WilsonReportingUnitOrbit
import YM.Integration.WilsonReportHarvestUpperSource
import YM.Integration.WilsonReportHarvestUpperAge

/-! The exact calibrated microscopic column of each specified measured lift,
with its original phase or with its physical normalization restored. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestUpperLabel
open Filter Lattice Wilson RG Source Extraction Spec RG12 RG17 RG05Readout Address Native
open Extra.Histories PhysicalNext.Repeat.Legato
open scoped Topology
variable {G:Gauge} {C:Family G} {order:Extraction.Order} {table:Table C.book} {F:Final C order table}

theorem actual (L:Layout F) (z:ℂ) (d:ℕ) (r:ℝ) (w:C.label d) (N per:ℕ) (U:Emblems C d) (live:L.level r ≤ N):
    Many.point U (WilsonReportingUpperChartPrice.returned F.room.cutoff (WilsonReportingUnitOrbit.primary d)
      (z • L.shift d r w) U (L.level r) N per) (L.level r) N =
    chunk (WilsonReportingUnitOrbit.primary d) ((C.factory d N per).terminal.symm
      ((z/(C.S.a (L.level r):ℂ)^d) • atRef L d r (N,per) w)) := by
  rw [WilsonReportingSpineCharge.carried F.room.cutoff live]
  exact congrArg (chunk (C:=C) (WilsonReportingUnitOrbit.primary d)) (WilsonReportingRegulatedFactory.upper L z d r w N per)

theorem unscaled (L:Layout F) (d:ℕ) (r:ℝ) (w:C.label d) (N per:ℕ) (U:Emblems C d) (live:L.level r ≤ N):
    Many.point U (WilsonReportingUpperChartPrice.returned F.room.cutoff (WilsonReportingUnitOrbit.primary d)
      ((C.S.a (L.level r):ℂ)^d • L.shift d r w) U (L.level r) N per) (L.level r) N =
    chunk (WilsonReportingUnitOrbit.primary d) ((C.factory d N per).terminal.symm (atRef L d r (N,per) w)) := by
  rw [actual L _ d r w N per U live,div_self (pow_ne_zero d (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')),one_smul]

/-- Restore the unscaled physical mark on the very same lift, uniformly before
the cutoff and period and with at most one further temperature power. -/
theorem paid (R:Run G) (simple:G.Simple) (h:ℕ):
    ∀ᶠ m:ℕ in atTop,∀d:ℕ,∀x:R.family.label d,
      mass R.family d (WilsonReportingUnitOrbit.phase • x) ≤ (R.family.path.levels.clock.hatBeta m)^h →
      mass R.family d ((R.family.S.a m:ℂ)^d • x) ≤ (R.family.path.levels.clock.hatBeta m)^(h+1) := by
  let z:=WilsonReportingUnitOrbit.phase
  have nz:z ≠ 0:=Suede.pitch_pos Suede.pip
  have normz:0<‖z‖:=norm_pos_iff.mpr nz
  filter_upwards [(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop ‖z‖⁻¹]
    with m finance d x price
  let β:=R.family.path.levels.clock.hatBeta m
  have small:R.family.S.a m ≤ 1:=by simpa only [Schedule.a_zero] using R.family.S.strictAnti.antitone (Nat.zero_le m)
  have factor:‖(R.family.S.a m:ℂ)^d‖ ≤ 1:=by
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (R.family.S.a_pos m)]
    exact pow_le_one₀ (R.family.S.a_pos m).le small
  calc
    _ = ‖(R.family.S.a m:ℂ)^d‖*mass R.family d x:=Extra.Histories.Size.smul _ _ _
    _ ≤ mass R.family d x:=mul_le_of_le_one_left (mass_nonneg ..) factor
    _ = ‖z‖⁻¹*mass R.family d (z • x):=by
      have same:mass R.family d (z • x)=‖z‖*mass R.family d x:=Extra.Histories.Size.smul _ _ _
      rw [same,←mul_assoc,inv_mul_cancel₀ normz.ne',one_mul]
    _ ≤ β*β^h:=mul_le_mul finance price (mass_nonneg ..)
      (zero_le_one.trans (R.family.path.levels.fits.delayed m).le)
    _ = _:=by rw [pow_succ,mul_comm]

end YM.Integration.WilsonReportHarvestUpperLabel
