import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundLogs
import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundMoments
import YM.Integration.WilsonLimitConstruction.FundedWilsonSparsePrice

/-! Effective-action and signed-observable payment on the original cofinal
schedule, before all cutoffs, periods, sparse fields, coarse configurations,
and bounded complex tests. The denominators are the original physical ones. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundPayment

open Function Filter MeasureTheory Lattice Wilson RG Exterior WilsonStartup
open MergeProof.Accent Extra.Trajectories PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonCouplingTransport FundedWilsonAtlas FundedWilsonSparseSupport
open FundedWilsonBackgroundEnvelope FundedWilsonBackgroundMoments
open scoped Topology Classical BigOperators
variable {G : Gauge}

theorem temperature (R : Run G) (N p : ℕ) : ((regulatorRun R.family N p N)^2)⁻¹ = R.family.beta N p := by
  have hb : 0 < R.family.beta N p :=
    (half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed N))).trans_le
      (R.makes.wilson.represents N p N le_rfl).band.1
  change (((Real.sqrt (R.family.beta N p))⁻¹)^2)⁻¹ = _
  rw [inv_pow,inv_inv,Real.sq_sqrt hb.le]

theorem window (R : Run G) (hG : G.Simple) (r s : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ i : ℕ in atTop, ∀ N p (hi : i ≤ N) (B : fieldDir G (R.family.side N p) 1),
      (links B).card ≤ s → (∀ j, ‖directions B j‖ ≤ 1) → ∀ V,
      let t := regulatorRun R.family N p N
      let q := ε*(regulatorRun R.family N p i)^((r:ℝ)+1-η)
      let y := carry R.family p N (R.family.path.β N p) (FundedWilsonBackgroundMeasure.approximate (r+2) B t) i hi V
      let w := (R.family.path.rep N p i).eval V
      0 < y ∧ ‖Real.log (y/w)‖ ≤ q ∧
        ∀ (O : Config G (R.family.side N p) → ℂ) (A : ℝ), Measurable O → (∀ U, ‖O U‖ ≤ A) →
          ‖carry R.family p N (R.family.path.β N p) (mark (FundedWilsonBackgroundMeasure.approximate (r+2) B t) O) i hi V -
            carry R.family p N (R.family.path.β N p) (mark (Wilson.bare (R.family.beta N p)) O) i hi V‖ ≤ q*A*w := by
  obtain ⟨c,hc,he⟩ := FundedWilsonBackgroundLogs.effective G r
  obtain ⟨d,hd,hm⟩ := FundedWilsonBackgroundMoments.purchase G r
  filter_upwards [FundedWilsonSparsePrice.prices R hG r s hc hε hη,
      FundedWilsonSparsePrice.prices R hG r s hd hε hη] with i H K N p hi B hs hB V
  let t := regulatorRun R.family N p N
  have h := H N p hi B hs
  have k := K N p hi B hs
  have Y := he R N p t h.1.ne' h.2.1 (temperature R N p) B hB i hi V
  refine ⟨Y.2.2.1,Y.2.2.2.trans h.2.2.1,fun O A hO hA => ?_⟩
  have ha : 0 ≤ A := (norm_nonneg (O 1)).trans (hA 1)
  have hw := (RG02.Actual.eval_pos R.makes.wilson hi V).le
  exact (hm R N p t k.1.ne' k.2.1 (temperature R N p) B hB O A hO hA i hi V).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k.2.2.2 ha) hw)

end YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundPayment
end
