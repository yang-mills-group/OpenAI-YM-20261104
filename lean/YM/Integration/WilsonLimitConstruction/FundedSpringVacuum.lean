import YM.Integration.ActualRunSpring
import YM.Integration.WilsonLimitConstruction.FundedChartPruning

/-! The actual original Spring supplies a pre-reset listing and source at
every physical step, together with its raw calendar bill, forced allowance
and equality to the original trajectory density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSpringVacuum

open Lattice Wilson RG RG.Shoot FullQLocal FullQLocal.RawInherited
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AnalyticBridge VerifiedReset Collection Next.Scheduling

variable {G : Gauge}

/-- The entire paid regular native Spring bill is covered by the degree-zero
raw shape at its literal coarse calendar index. -/
theorem forecast (L : Levels G) (m : ℕ) : Time.forecastE L m ≤ shape L.clock 0 m := by
  have hg := WardBin.stepG L m
  have h1 : L.clock.hatCoupling m ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (L.fits.delayed m).le)
  have hc : Time.credit G (L.params m) ≤ 1 :=
    (Time.authorized G (L.params m)).1.trans (by norm_num)
  have hu := add_nonneg (hg.le.trans (WardBin.stepGle L m)) (sq_nonneg ((L.clock.monitor m)⁻¹))
  calc
    _ ≤ 1 * (L.clock.hatCoupling m)^((11:ℝ)/5) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hg.le _)
    _ ≤ L.clock.hatCoupling m := by
      simpa only [one_mul,Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hg h1 (show (1:ℝ) ≤ 11/5 by norm_num)
    _ ≤ _ := by
      simp only [shape,pow_zero,one_mul]
      linarith only [hu]

/-- One already selected Spring on this Run, before any marker census,
supplies the same signed source, raw estimate and full original vacuum density. -/
theorem actual (R : Run G) (hG : G.Simple) (N p m : ℕ) (hm : m < N) :
    let P := ActualRunSpring.selected R N p m hm
    let L := R.family.path.levels
    Collection.Local P.spring.X' (L.budget m) (P.spring.V' P.point.val)
      (shape L.clock 0 m) (L.clock.forcedAllowance m) ∧
    (R.family.path.rep N p m).eval = earlyValue P.spring.X' (R.alloy.B.kin.path N m)
      (L.params m).clip (L.budget m) (P.spring.V' P.point.val)
      (R.family.path.rep N p (m+1)).beta (P.spring.τ P.point.val) (R.alloy.B.kin.alpha N m) := by
  intro P L
  have hsource := P.spring.core hm P.point.val P.point.property
  have hfees := (R.kit.machine.passes hm P.spring.knows).1
  constructor
  · exact RG01Estimate.VacuumListing.relax _ hsource (forecast L m)
      (RG01Estimate.VacuumPrices.forecast_allowance R.kit hm (P.spring.knows _ P.point.property).2)
  · rw [P.coarse,P.fine,P.spring.owns hG hm P.point.property]
    exact hsource.actual hG (R.alloy.B.support.cap N m hm.le) hfees.decent hfees.width _
      (Return.enough_room ..) (hfees.fees _ P.point.property) _ _

end YM.Integration.WilsonLimitConstruction.FundedSpringVacuum
end
