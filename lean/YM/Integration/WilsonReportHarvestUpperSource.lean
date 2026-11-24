import YM.Integration.WilsonReportingSpineCharge
import YM.Integration.WilsonReportHarvestSourceReach

/-! A before-period bill for the original returned marked-spine source,
with its signed measured cutoff coordinate preserved. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestUpperSource
open Function Filter Lattice RG Source RG12 RG05Readout Address Native Harvest
open WilsonReportHarvestSourceReach
open scoped Classical Topology
variable {G:Gauge} {C:Family G} (hC:C.Makes)

theorem original (D h:ℕ) :
    ∀ᶠ m:ℕ in atTop, ∀ b N per s:ℕ, ∀ rail:Rail C, ∀ B:ℕ→ℕ→ℝ,
      ∀ V:Sight C s per, ∀ U:Emblems C s, Spine rail B hC b per s N V U →
      ∀ t:Letter s, ∀ x:C.label (kept t), C.ref (kept t) ≤ m → b ≤ m →
      m ≤ N → s ≤ D → mass C (kept t) x ≤ (C.path.levels.clock.hatBeta m)^h →
      size (WilsonReportingUpperChartPrice.returned hC t x U m N per) ≤
        (C.path.levels.clock.hatBeta m)^h*(C.S.a m/C.S.a N)^(D+2) ∧
      Many.point U (WilsonReportingUpperChartPrice.returned hC t x U m N per) m N =
        chunk t (WilsonReportingFactorySingleton.upper hC (kept t) m N per x) := by
  filter_upwards [string_paid (C:=C) (show 0 < (1:ℝ) by norm_num)] with m funded
  intro b N per s rail B V U spine t x age begun live small paid
  refine ⟨?_,WilsonReportingSpineCharge.carried hC live t x⟩
  let a:=C.S.a m/C.S.a N
  let β:=C.path.levels.clock.hatBeta m
  have ap:0<a:=div_pos (C.S.a_pos m) (C.S.a_pos N)
  have aa:1 ≤ a:=(one_le_div (C.S.a_pos N)).2 (C.S.strictAnti.antitone live)
  have bp:0 ≤ β:=zero_le_one.trans (C.path.levels.fits.delayed m).le
  have cost:stringCost C live ≤ a:=by
    simpa only [one_mul,←mesh,elapsed,a] using funded N live
  have pow:a^(s+2) ≤ a^(D+2):=pow_le_pow_right₀ aa (by omega)
  calc
    _ ≤ stringCost C live*a^(s+1)*mass C (kept t) x :=
      WilsonReportingUpperChartPrice.signed hC spine t x age begun live
    _ ≤ (a*a^(s+1))*β^h:=mul_le_mul
      (mul_le_mul_of_nonneg_right cost (pow_nonneg ap.le _)) paid (mass_nonneg ..) (mul_nonneg ap.le (pow_nonneg ap.le _))
    _ = β^h*a^(s+2):=by rw [pow_succ a (s+1)];ring
    _ ≤ _:=mul_le_mul_of_nonneg_left pow (pow_nonneg bp _)

end YM.Integration.WilsonReportHarvestUpperSource
