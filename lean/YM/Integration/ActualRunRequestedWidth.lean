import YM.Integration.OriginalRunProfile
import YM.Integration.ActualRunSpring
import YM.Integration.ActualRunAdmissionScales

/-!
The actual machine of the original Run supplies native geometry at every
calendar level. Its retained constructor profile then admits any fixed
requested support exponent on one tail. All radii, fields, kernels and
physical representatives stay unchanged.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunRequestedWidth

open Filter Lattice RG Wilson WilsonStartup
open PhysicalNext.Repeat.Legato
open PhysicalNext.ThroughLaunch
open AnalyticBridge VerifiedReset
open ActualRunAdmissionScales OriginalRunConstruction
open scoped Topology

variable {G : Gauge}

/-- Geometry is a calendar property of the same machine. A single actual
step at N=m+1 supplies it; no new trajectory is chosen. -/
theorem native_geometry (R : Run G) (m : ℕ) :
    Decent (R.family.path.levels.params m).clip
        (R.family.path.levels.budget m) ∧
      Geo.Width (R.family.path.levels.budget m)
        (R.family.path.levels.params m).clip
        (R.family.path.levels.params m).width := by
  let Q := ActualRunSpring.selected R (m+1) 0 m (Nat.lt_succ_self m)
  have h := (R.kit.machine.passes (Nat.lt_succ_self m) Q.spring.knows).1
  exact ⟨h.decent, h.width⟩

/-- The requested budget has the same block scale and threshold. Its smaller
support exponent preserves the actual geometric width inequality. -/
theorem width_of_support_le (R : Run G) (m ord pow : ℕ) (supp : ℝ)
    (hord : 6 ≤ ord) (hpow : 2 ≤ pow) (hsupp : 0 < supp)
    (hsmall : supp ≤ (R.family.path.levels.budget m).supportExponent) :
    Geo.Width (requestedBudget R.family.path.levels m ord pow supp hord hpow hsupp)
      (R.family.path.levels.params m).clip
      (R.family.path.levels.params m).width := by
  obtain ⟨_, hw⟩ := native_geometry R m
  refine ⟨hw.1, hw.2.1, ?_⟩
  change (supp+1) / ((R.family.path.levels.budget m).B : ℝ) ≤
    (R.family.path.levels.params m).width / 4
  exact (div_le_div_of_nonneg_right (add_le_add hsmall (le_refl (1 : ℝ)))
    (Nat.cast_nonneg (R.family.path.levels.budget m).B)).trans hw.2.2

/-- One original-calendar tail admits any fixed requested support exponent.
The tail is before all cutoffs, periods, fields and test functions. -/
theorem eventually_support (R : Run G)
    (hprofile : WithStage R.metals.p originalOrders) (supp : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      supp ≤ (R.family.path.levels.budget m).supportExponent := by
  obtain ⟨k, hk⟩ := exists_nat_ge supp
  filter_upwards [R.family.path.levels.fits.deep.eventually_ge_atTop k] with m hm
  change supp ≤
    (R.alloy.B.a.clock.stage (R.alloy.B.a.clock.J m)).supportExponent
  rw [R.alloy.B.valid.stage, hprofile.prices]
  change supp ≤ 100 + (R.alloy.B.a.clock.J m : ℝ)
  have hmk : (k : ℝ) ≤ (R.alloy.B.a.clock.J m : ℝ) := by exact_mod_cast hm
  linarith

/-- Actual native Decent and the fixed requested Width hold together on the
same tail, with no new geometric or scalar-smallness premise. -/
theorem eventually_geometry (R : Run G)
    (hprofile : WithStage R.metals.p originalOrders)
    (ord pow : ℕ) (supp : ℝ)
    (hord : 6 ≤ ord) (hpow : 2 ≤ pow) (hsupp : 0 < supp) :
    ∀ᶠ m : ℕ in atTop,
      Decent (R.family.path.levels.params m).clip
        (R.family.path.levels.budget m) ∧
      Geo.Width (requestedBudget R.family.path.levels m ord pow supp hord hpow hsupp)
        (R.family.path.levels.params m).clip
        (R.family.path.levels.params m).width := by
  filter_upwards [eventually_support R hprofile supp] with m hm
  exact ⟨(native_geometry R m).1,
    width_of_support_le R m ord pow supp hord hpow hsupp hm⟩

end YM.Integration.ActualRunRequestedWidth
end
