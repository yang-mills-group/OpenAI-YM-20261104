import YM.Integration.ActualRunRequestedWidth
import YM.Integration.ActualRunQLocalAdmission

/-! The retained readout purchase pays every fixed requested support directly.
The original budget scale and native width are unchanged; no prescribed
support profile or new trajectory is required. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunReadoutWidth

open Filter Lattice RG Wilson WilsonStartup
open PhysicalNext.Repeat.Legato
open AnalyticBridge VerifiedReset
open ActualRunAdmissionScales ActualRunAdmissionClock
open scoped Topology

variable {G : Gauge}

/-- One tail before all cutoffs and periods supplies native Decent and the
requested Width. The existing preMesh envelope pays the support ratio. -/
theorem eventually_geometry (R : Run G) (hG : G.Simple)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (ord pow : ℕ) (supp : ℝ)
    (hord : 6 ≤ ord) (hpow : 2 ≤ pow) (hsupp : 0 < supp) :
    ∀ᶠ m : ℕ in atTop,
      Decent (R.family.path.levels.params m).clip
        (R.family.path.levels.budget m) ∧
      Geo.Width (requestedBudget R.family.path.levels m ord pow supp hord hpow hsupp)
        (R.family.path.levels.params m).clip
        (R.family.path.levels.params m).width := by
  let A := R.family.path.levels
  have hMesh : PreMesh A := ActualRunQLocalAdmission.actual_preMesh R hReadout
  have hD : 0 < 4 * (supp + 1) := by positivity
  filter_upwards [rate_scale A hG (4 * (supp + 1)) hD,
    (Real.tendsto_log_atTop.comp (WardBin.bell A hG)).eventually_ge_atTop 1]
    with m hscale hlog
  have hw : 0 < (A.params m).width := (A.params m).width_pos
  have he : 1 ≤ ActualRunAdmissionClock.envelope A m :=
    (profileCost_one A m).trans (profile_coarse A hG hMesh m)
  have hi : (A.params m).width⁻¹ ≤ ActualRunAdmissionClock.envelope A m :=
    (profileCost_components A m).1.trans (profile_coarse A hG hMesh m)
  have hpaid : 4 * (supp + 1) * (A.params m).width⁻¹ ≤
      Real.log (A.clock.hatBeta m) :=
    (mul_le_mul_of_nonneg_left hi hD.le).trans
      ((mul_le_mul_of_nonneg_left (show ActualRunAdmissionClock.envelope A m ≤ 1 + 2 * ActualRunAdmissionClock.envelope A m by
        linarith) hD.le).trans hscale)
  have hcover : (Real.log (A.clock.hatBeta m))^2 ≤
      (A.clock.coverSize m : ℝ) := Nat.le_ceil _
  have hl : 1 ≤ Real.log (A.clock.hatBeta m) := hlog
  have hlogCover : Real.log (A.clock.hatBeta m) ≤ (A.clock.coverSize m : ℝ) := by
    exact (le_mul_of_one_le_right (zero_le_one.trans hl) hl).trans
      (by simpa only [pow_two] using hcover)
  have hproduct : 4 * (supp + 1) ≤ (A.clock.coverSize m : ℝ) * (A.params m).width :=
    (div_le_iff₀ hw).mp (by
      simpa only [div_eq_mul_inv] using hpaid.trans hlogCover)
  obtain ⟨hd, hn⟩ := ActualRunRequestedWidth.native_geometry R m
  refine ⟨hd, hn.1, hn.2.1, ?_⟩
  change (supp + 1) / ((A.budget m).B : ℝ) ≤ (A.params m).width / 4
  have hB : 0 < ((A.budget m).B : ℝ) := by exact_mod_cast (A.budget m).B_pos
  apply (div_le_iff₀ hB).mpr
  change supp + 1 ≤ (A.params m).width / 4 * (A.clock.coverSize m : ℝ)
  nlinarith

end YM.Integration.ActualRunReadoutWidth
end
