import YM.Integration.ActualOriginalQInitialInput
import YM.Integration.ActualRunAdjacentCoupling
import YM.Integration.WilsonReportHarvestUpperRange
import YM.Integration.WilsonLimitConstruction.FundedCoverStepPrice
import YM.Integration.ManuscriptQLocalHealthyRate

/-! Uniform payment of the two native test-radius losses at the first nonbare
date. The successor carries the previous kernel prices from the same registered
bank, and its native radius receipt takes the full available radius. -/
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldFirstRadii
open Filter Lattice Wilson RG Source Marker Precision Pert.Asymptotics IterationFour
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open MergeProof MergeProof.Accent
open scoped Topology Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (R : Run G) (hG : G.Simple)

/-- A fixed real earlier reference includes the first genuinely nonbare date
in the original logarithmic upper interval once the cutoff is large. -/
theorem eligible (b : ℕ) : ∀ᶠ j : ℕ in atTop,
    WilsonReportHarvestUpperRange.eligible R.family.S b j (j+1) := by
  let L := R.family.path.levels
  filter_upwards [L.fits.mesh.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    L.S.divergent.eventually_gt_atTop 0, L.S.divergent.eventually_ge_atTop (2*L.S.scale b)]
    with j step pos wide
  have one : Real.log (L.S.block j).val ≤ (1/2:ℝ)*L.S.scale j := (div_le_iff₀ pos).mp step
  change L.S.scale (j+1)-L.S.scale b ≤ 2*(L.S.scale j-L.S.scale b)
  rw [Schedule.scale_succ]
  linarith

omit [DecidableEq V] [Fintype V] in
private theorem cost {J : Request V} (A : NumericSchedule R.family J) (j : ℕ) :
    A.radiusLoss j ≤ A.admittedCost j := by
  linarith only [A.cost_covers_widths j, (inv_pos.mpr (A.input_width_pos j)).le,
    (inv_pos.mpr (A.output_width_pos j)).le]

include hG in
omit [DecidableEq V] in
/-- The extra power two pays the complete test loss on every face, before the
period and cutoff and without restricting any exterior field. -/
theorem adjacent {J J' : Request V} (A : NumericSchedule R.family J)
    (A' : NumericSchedule R.family J') :
    ∀ᶠ m : ℕ in atTop, ∀ N per, m+1<N → ∀ s : Finset V,
      (A.radiusLoss (m+1)*A'.radiusLoss m)^s.card*(regulatorRun R.family N per (m+1))^2 ≤ 2 := by
  obtain ⟨l, old⟩ := ManuscriptQLocalHealthyRate.absorb A (Fintype.card V) 1 1 zero_lt_one
  obtain ⟨l', next⟩ := ManuscriptQLocalHealthyRate.absorb A' (Fintype.card V) 1 1 zero_lt_one
  have small := Currency.g_small hG R.makes 1 zero_lt_one
  have ratio := (tendsto_add_atTop_nat 1).eventually (ActualRunAdjacentCoupling.eventually_ratio R hG)
  filter_upwards [eventually_ge_atTop l, eventually_ge_atTop l',
    (tendsto_add_atTop_nat 1).eventually small, (tendsto_add_atTop_nat 2).eventually small,
    ratio] with m ml ml' tiny₁ tiny₂ prices
  intro N per hN s
  let g₁ := regulatorRun R.family N per (m+1)
  let g₂ := regulatorRun R.family N per (m+2)
  have gp : 0<g₁ := Currency.g_pos R.makes N per (m+1) hN.le
  have hp : 0<g₂ := Currency.g_pos R.makes N per (m+2) hN
  have gnear : g₁ ≤ 2*g₂ := by
    have := (le_div_iff₀ gp).mp (prices N per hN).1
    change (1/2:ℝ)*g₁ ≤ g₂ at this
    linarith
  have a : A.admittedCost (m+1)^(Fintype.card V)*g₂ ≤ 1 := by
    simpa [g₂] using old (m+1) (by omega) N per hN hp (tiny₂ N per hN).le
  have b : A'.admittedCost m^(Fintype.card V)*g₁ ≤ 1 := by
    simpa [g₁] using next m ml' N per (by omega) gp (tiny₁ N per hN.le).le
  have upper (j : ℕ) {J'' : Request V} (D : NumericSchedule R.family J'') :
      D.radiusLoss j^s.card ≤ D.admittedCost j^(Fintype.card V) :=
    (pow_le_pow_left₀ (D.radius_loss_positive j).le (cost R D j) s.card).trans
      (pow_le_pow_right₀ (D.admitted_cost_ge_one j) (Finset.card_le_univ s))
  have o : A.radiusLoss (m+1)^s.card*g₁ ≤ 2 := by
    calc
      _ ≤ A.admittedCost (m+1)^(Fintype.card V)*(2*g₂) :=
        mul_le_mul (upper _ A) gnear gp.le (pow_nonneg (A.admitted_cost_nonnegative _) _)
      _ = 2*(A.admittedCost (m+1)^(Fintype.card V)*g₂) := by ring
      _ ≤ 2 := by linarith
  have n : A'.radiusLoss m^s.card*g₁ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (upper _ A') gp.le).trans b
  have nn : 0 ≤ A'.radiusLoss m^s.card*g₁ := mul_nonneg (pow_nonneg (A'.radius_loss_positive _).le _) gp.le
  change (A.radiusLoss (m+1)*A'.radiusLoss m)^s.card*g₁^2 ≤ 2
  rw [mul_pow]
  calc
    _ = (A.radiusLoss (m+1)^s.card*g₁)*(A'.radiusLoss m^s.card*g₁) := by ring
    _ ≤ 2*1 := mul_le_mul o n nn (by norm_num)
    _ = 2 := by norm_num

variable {B : MS.Local.Physical.Deck G} (u : V → MS.Rake.Label B)
  (J : Request V) (A : NumericSchedule R.family J)
local notation "startF" => ActualOriginalQInitialInput.input R hG u J A
local notation "startA" => ActualOriginalQInitialInput.schedule R hG u J A

/-- The old kernel cost and test radius here belong to the original marked
MS source with all its proper lower-grade counterterms. -/
theorem initial (d : LocalFormal.Datum R.family (Stock.census V))
    (Q : MS.Land.Prescription B) (o : V → Site (R.family.side (d.level+1) d.period))
    (μ : ℝ) (ks : V → ℕ) (ord : ∀ k, k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
    (first : ActualOriginalQInitialInput.start R hG u J A ord ≤ d.level)
    (per : (ActualOriginalQPointSetup.request R u J).physicalPeriodLower ≤ (R.family.S.period d.period).val) :
    (startF d Q o μ ks ord first per).outputRadii = (fun _ => ((startA).radiusLoss d.level)⁻¹) ∧
    (startF d Q o μ ks ord first per).kernelCosts = (fun _ => 1) :=
  ⟨rfl,rfl⟩

end YM.Integration.WilsonReportingPrescribedOldFirstRadii
