import YM.Integration.OriginalCensusActivities
import YM.Integration.CensusBarcodeComparison
import YM.Integration.OriginalForcedWidth

/-! The signed tested discrepancy of the actual native hard sectors on
every intermediate torus, at the original support and marked inventory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalCensusBarcode

open Filter Lattice Wilson WilsonStartup RG RG.Shoot Marker MergeProof
open AnalyticBridge VerifiedReset Collection
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG01Estimate RG01Estimate.CensusStep ConnectedActivityE6.Coat Push.SectorMeasure
open IterationFour IterationFour.Vacuum Extra.Iteration UVNext.CouplingReset
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction.FundedCensusVacuum Pert.Asymptotics
open CensusBarcodeComparison
open scoped Topology

variable {G : Gauge} {V : Type} {J : Request V}

def carrier (R : Run G) (A : NumericSchedule R.family J) (m N per : ℕ) (hN : m < N) :
    Rep G (R.family.side m per) :=
  let S := station R N per m hN
  let Y := R.family.path.rep N per m
  let X := ledger R.kit S.guide
  let D := discarded R.kit S.guide S.guide S.identity J.order
  let b := Y.beta - Averaging.delta (X.read D)
  CenteredCensusVacuum.record Y (Reset.after (R.alloy.B.kin.path N m)
    (R.alloy.B.a.params m).clip (A.outputNorm m) X D b 0 0)

def Tested (R : Run G) (A : NumericSchedule R.family J) (ρ C : ℝ) (p d m N per : ℕ)
    (hN : m < N) : Prop :=
  let q := A.outputNorm m
  let Y := R.family.path.rep N per m
  let Z := carrier R A m N per hN
  let L := R.family.path.levels
  let κ := Real.sqrt (L.clock.forcedAllowance m)
  let w := Push.Local.hitWidth (L.budget m)
  let g := regulatorRun R.family N per m
  ∀ v : ℝ, 0 ≤ v → v ≤ C/g^d → ∀ (o : Site _) (z : Config G _) (stem : Box _ → ℂ),
    (∀ a, ‖stem a‖ ≤ w*v) →
      SumBudget (fun a => charge q o a
        ‖(native Y.activities z a-native Z.activities z a)*stem a/(κ:ℂ)‖) (ρ*g^p)

theorem atStation (R : Run G) (A : NumericSchedule R.family J) {ε : ℝ}
    (hr : J.outputSupport ≤ (R.family.path.levels.budget 0).supportExponent)
    {ρ C : ℝ} (p d m N per : ℕ) (hN : m < N)
    (hs : OriginalCensusFusion.AtStation R A ε m N per hN)
    (hprice : ∀ v : ℝ, v ≤ C/(regulatorRun R.family N per m^d) →
      OriginalForcedWidth.factor R m*v ≤ ρ*regulatorRun R.family N per m^p) :
    Tested R A ρ C p d m N per hN := by
  unfold Tested
  intro q Y Z L κ w g v hv hbill o z stem hstem
  have hy : R.family.path.Conv N per m := R.makes.wilson.represents N per m hN.le
  have hB : q.B = Y.p.B := by rw [hy.vac];exact (A.output_norm m).block
  have hσ : q.supportExponent ≤ Y.p.supportExponent := by
    rw [hy.vac]
    exact (A.output_norm m).reserve.le.trans (hr.trans (L.fits.deepExp (Nat.zero_le m)))
  let γ := L.clock.forcedAllowance m
  have hY : Y.activities.KBound q γ :=
    CensusBarcodeComparison.restrict _ _ _ hB hσ hy.good.labels.boundK
  obtain ⟨_,hz⟩ := CenteredCensusVacuum.atStation R A ε m N per hN hs
  have hZ : Z.activities.KBound q γ := (hz Y.beta).2.2.2.2.2.2.1.labels.boundK
  have hκ : 0 < κ := Real.sqrt_pos.2 (Real.exp_pos _)
  have hw : 0 ≤ w := Nat.cast_nonneg _
  have h := CensusBarcodeComparison.tested _ _ q hY hZ hκ (mul_nonneg hw hv) o z stem hstem
  refine ⟨h.1,h.2.1,h.2.2.trans ?_⟩
  calc
    _ = OriginalForcedWidth.factor R m*v := by change (γ+γ)/κ*(w*v) = 2*(γ/κ)*w*v;ring
    _ ≤ _ := hprice v hbill

/-- Uniform in the stopping level, upper cutoff, period, base field,
original barcode, normalized Taylor stem, and every intervening step. -/
theorem interval (R : Run G) (hG : G.Simple) (A : NumericSchedule R.family J)
    {ε ρ C : ℝ} (hr : J.outputSupport ≤ (R.family.path.levels.budget 0).supportExponent)
    (hs : OriginalCensusFusion.AtOrder R A ε) (p d : ℕ) (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ first : ℕ, ∀ i N : ℕ, first ≤ i → i ≤ N → ∀ per m : ℕ, i ≤ m →
      ∀ hN : m < N, OriginalCensusActivities.Physical R A ε ρ p m N per hN ∧
        Tested R A ρ C p d m N per hN := by
  have hall := hs.and ((OriginalForcedFlat.allowance R hG p hρ).and
    (OriginalForcedWidth.withStem R hG p d hC hρ))
  obtain ⟨first,hfirst⟩ := eventually_atTop.1 hall
  refine ⟨first,fun i N hi _ per m hm hN => ?_⟩
  obtain ⟨h,hf,hb⟩ := hfirst m (hi.trans hm)
  exact ⟨OriginalCensusActivities.station R A ε ρ p m N per hN (h N per hN) (hf N per hN.le),
    atStation R A hr p d m N per hN (h N per hN) (hb N per hN.le)⟩

end YM.Integration.OriginalCensusBarcode
end
