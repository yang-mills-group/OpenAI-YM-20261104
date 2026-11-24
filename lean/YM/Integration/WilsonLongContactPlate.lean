import YM.Integration.WilsonLongContactProtectedRun
import YM.Integration.WilsonLongContactWeighted

/-! The authentic Heir footprint compression on every originally declared merged
address, including addresses too long for a protected angular chamber. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactPlate
open Function Filter Set Lattice Wilson Pressure RG Tree Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open PhysicalNext.JointLoad.Psalm Supply Input Org Testing
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open QLocalRequestedHeirQuote QLocalRequestedHeirPurchase QLocalRequestedSectorSale
open WilsonLongContactRebudget WilsonLongContactSectorProtection WilsonLongContactProtectedRun
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] {J : Request V}
variable {Δ : Daisy.Charity.RG12.Decal G} {extra : Stage → ℕ → ℝ} {γ : ℝ} {R : Run G}
    {ρ : Premium G J.outputFieldOrder}
    {paid : WilsonLongContactSectorProtection.Paid J Δ extra γ ρ R.kit}
    {A : NumericSchedule R.family J} {Γ : Census V} {z : LocalFormal.Datum R.family Γ}
local notation "x₀" => R.alloy.B.a.clock.hatBeta z.level
local notation "Y₁" => R.family.path.rep z.cutoff z.period (z.level+1)

abbrev coarse (e : Field J Δ extra γ R ρ paid A z) (i : ℕ) : ℕ :=
  coverNumber (A.outputNorm z.level).B (Brim.plate e.cash.choose i).support

abbrev fine (A : NumericSchedule R.family J) (z : LocalFormal.Datum R.family Γ) (i : ℕ) : ℕ :=
  coverNumber (A.inputNorm z.level).B ((R.family.path.rep z.cutoff z.period (z.level+1)).activities.reg i).support

theorem compressed (e : Field J Δ extra γ R ρ paid A z) (i : ℕ) :
    toll J * coarse e i ≤ Release.base (toll J) 505 +
      ((A.inputNorm z.level).supportExponent/2) * fine A z i := by
  have chosen := reported J Δ extra γ R ρ paid z
  have accepts := (QLocalRequestedSectorCalendar.record_at J Δ extra γ R A z _
    chosen.1.window chosen.2).2.1
  have pos : 0≤toll J := by unfold QLocalRequestedHeirQuote.toll; linarith [J.output_support_pos]
  have width := (A.output_norm z.level).block
  exact Release.compressed pos accepts
    (Brim.billboard e.cash.choose (show 500+5≤505 by decide) i) width
    (by rw [width];exact e.plays.rehearsed.weft.cover)

theorem split_weight {a b C F K s : ℝ} (ha : 0≤a) (h : a*C≤K+(b/2)*F) :
    s≤C → Real.exp ((a/2)*C) * Real.exp ((b/2)*F) ≤
      Real.exp (K-(a/2)*s) * Real.exp (b*F) := by
  intro hs
  rw [←Real.exp_add,←Real.exp_add]
  apply Real.exp_monotone
  linarith [mul_le_mul_of_nonneg_left hs ha]

theorem large (e : Field J Δ extra γ R ρ paid A z) (i : ℕ) (w : ℝ) (hw : 0≤w)
    (h : (A.outputNorm z.level).B<coarse e i) :
    (Real.exp ((toll J/2)*coarse e i)*Real.exp (((A.inputNorm z.level).supportExponent/2)*fine A z i))*w ≤
      Real.exp (Release.base (toll J) 505-(toll J/2)*(A.outputNorm z.level).B) *
        (Real.exp ((A.inputNorm z.level).supportExponent*fine A z i)*w) := by
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right (split_weight (by unfold QLocalRequestedHeirQuote.toll; linarith [J.output_support_pos])
    (compressed e i) (Nat.cast_le.mpr h.le)) hw

end YM.Integration.WilsonLongContactPlate
