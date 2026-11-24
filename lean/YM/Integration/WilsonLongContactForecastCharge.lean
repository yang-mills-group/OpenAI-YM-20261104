import YM.Integration.WilsonLongContactHymnTariff

/-! The genuine pre-block scalar allowance includes engineering and the movement of the support. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactForecastCharge
open Function Filter Set Lattice Wilson RG Pressure Tree Precision Marker Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Lotus
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling Supply Input Testing
open AnalyticBridge VerifiedReset ConnectedActivityE6
open WilsonLongContactSectorProtection WilsonLongContactProtectedRun
open QLocalRequestedHeirQuote QLocalRequestedHeirPurchase IterationFour Pert.Asymptotics
open WilsonLongContactPlate
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] {J : Request V}
    {Δ : Daisy.Charity.RG12.Decal G} {extra : Stage → ℕ → ℝ} {γ : ℝ} {R : Run G}
    {ρ : Premium G J.outputFieldOrder} {paid : WilsonLongContactSectorProtection.Paid J Δ extra γ ρ R.kit}
    {A : NumericSchedule R.family J} {Γ : Census V} {z : LocalFormal.Datum R.family Γ}
local notation "S₀" => R.alloy.B.a.clock.op z.level z.period
local notation "T₀" => ships R.alloy.B z.cutoff z.level z.period
local notation "Y₁" => R.family.path.rep z.cutoff z.period (z.level+1)
local notation "p₀" => A.outputNorm z.level
local notation "p₁" => A.inputNorm z.level
local notation "ℓ₁" => R.alloy.B.a.clock.J (z.level+1)
local notation "ℓ₀" => R.alloy.B.a.clock.J z.level
local notation "C₀" => libretto J R.metals.p R.metals.K (ℓ₁) (ℓ₀)
local notation "b₀" => paid.choose (ℓ₁) (ℓ₀)
local notation "u₁" => regulatorRun R.family z.cutoff z.period (z.level+1)


def invoice (J : Request V) (φ : Forecast G J.outputFieldOrder) (h : ℕ) (δ : ℝ) :
    Premium G J.outputFieldOrder :=
  fun Q D C b x=>∃ v : ℝ, Real.exp (Release.base (toll J) 505)*(D.L.val:ℝ)^h* |v|≤δ ∧ φ Q D C b x v

omit [DecidableEq V] in
theorem prepaid (φ : Forecast G J.outputFieldOrder) (h : ℕ) {δ : ℝ} (positive : 0<δ)
    (original : ∀ {P : Teller G} (Q : ConnectedActivityE6.Target G P) (D : Patch)
      (C : Libretto G J.outputFieldOrder) (b : QLocalRequestedSectorSale.Booking G),
      D.Branches P.bind G → b.record.ε≤1/4 →
      ∃ k : ℝ→ℝ, Rate G D.L (-(1/2:ℝ)) k ∧ ∀ᶠ x : ℝ in atTop, φ Q D C b x (k x)) :
    Admitted J (invoice J φ h δ) := by
  intro P Q D C b branch cap
  obtain ⟨k,hk,sale⟩ := original Q D C b branch cap
  let mult := Real.exp (Release.base (toll J) 505)*(D.L.val:ℝ)^h
  have multpos : 0 < mult := by unfold mult; positivity
  filter_upwards [hk.below (by norm_num) (δ / mult) (div_pos positive multpos), sale] with x small bought
  refine ⟨k x,?_,bought⟩
  change mult * |k x| ≤ δ
  rw [mul_comm]; exact (le_div_iff₀ multpos).mp small

theorem spatial (e : Field J Δ extra γ R ρ paid A z) (i h : ℕ) {v δ w : ℝ} (hw : 0≤w)
    (buy : Real.exp (Release.base (toll J) 505)*((S₀).patch.L.val:ℝ)^h* |v|≤δ) :
    Real.exp (toll J*coarse e i) * (((S₀).patch.L.val:ℝ)^h*(|v| *w)) ≤
      δ*(p₁).mass ((Y₁).activities.reg i).support w := by
  have geom := compressed e i
  have sign : 0≤(p₁).supportExponent * (fine A z i:ℝ) := mul_nonneg (p₁).exponent_pos.le (Nat.cast_nonneg _)
  have he : Real.exp (toll J*coarse e i) ≤ Real.exp (Release.base (toll J) 505) *
      Real.exp ((p₁).supportExponent * (fine A z i:ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_monotone
    linarith only [geom,sign]
  calc
    _ ≤ (Real.exp (Release.base (toll J) 505) * Real.exp ((p₁).supportExponent*(fine A z i:ℝ))) *
        (((S₀).patch.L.val:ℝ)^h*(|v| *w)) := mul_le_mul_of_nonneg_right he (by positivity)
    _ = (Real.exp (Release.base (toll J) 505) * ((S₀).patch.L.val:ℝ)^h * |v|) *
        ((p₁).mass ((Y₁).activities.reg i).support w) := by unfold BudgetPoint.mass; unfold WilsonLongContactPlate.fine; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right buy (mul_nonneg (Real.exp_pos _).le hw)

end YM.Integration.WilsonLongContactForecastCharge
