import YM.Integration.WilsonLongContactFrozenResponse
import YM.Integration.WilsonLongContactForecastCharge

/-! The original physical enrollment specializes before cutoff and period to a small occupied plate. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactNearSchedule
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



open WilsonLongContactRebudget Blaze Next.Foundations Brim WilsonLongContactForecastCharge
open YM.PhysicalNext.Repeat.WilsonLongContactFrozenGaussian
open Planned.AtomRegular.Sample WardBin.Lies
open WilsonLongContactTown
variable (J) (κ χ : Chi)

/-- The empty duplicate-mask subcase of the original held Gaussian comparison. -/
def assay : Forecast G J.outputFieldOrder := fun {P} Q D C b x v=>
  ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D →
    ∀ (Qf : Rep G f) (α : ℝ) (H : Cash b.W x b.μ D.L Q b.order α T Qf)
    (F : Forest S.ratio) (i : ℕ) (W : Config G c) (z : S.Choices) (B : BudgetPoint),
    B.B=radiusB x → B.power=J.outputDistanceOrder → Plays C b.record B Qf.p P T x →
    ∀ o∈(Brim.plate H i).support,
      coverNumber (radiusB x) (Brim.plate H i).support≤radiusB x →
      Healthy B.threshold (Brim.plate H i).support W →
      ∀ j (Z : Slab G c j), j≤J.outputFieldOrder → (∀ a,B.dirBound o (Z a)) →
      (∀ a, ‖Z a‖≤Brim.canopyW G D.L J.outputDistanceOrder x) →
      allowance (Brim.foyer H i F χ W z) i (Brim.mapcase H i F)
        b.order.a v b.record κ (journey W j Z) J.outputFieldOrder

variable {J}
local notation "x₁" => R.alloy.B.a.clock.hatBeta z.level

theorem held (h : ℕ) (δ : ℝ)
    (paid : WilsonLongContactSectorProtection.Paid J Δ extra γ (invoice J (assay J (G:=G) κ χ) h δ) R.kit)
    (e : Field J Δ extra γ R (invoice J (assay J (G:=G) κ χ) h δ) paid A z) :
    ∃ v : ℝ, Real.exp (Release.base (toll J) 505)*((S₀).patch.L.val:ℝ)^h * |v|≤δ ∧
    ∀ (i : ℕ) (F : Forest (S₀).ratio) (tag : (S₀).Choices) (W : Config G (R.family.S.side z.level z.period))
      (o : Site (R.family.S.side z.level z.period)), o∈(Brim.plate e.cash.choose i).support →
      coarse e i≤(p₀).B → Healthy (p₀).threshold (Brim.plate e.cash.choose i).support W →
      ∀ j (Z : Slab G _ j), j≤J.outputFieldOrder → (∀ a,(p₀).dirBound o (Z a)) →
      (∀ a t,t.1∉(Brim.plate e.cash.choose i).support→Z a t=0) →
      allowance (Brim.foyer e.cash.choose i F χ W tag) i (Brim.mapcase e.cash.choose i F)
        (paid.choose (ℓ₁) (ℓ₀)).order.a v (paid.choose (ℓ₁) (ℓ₀)).record κ (journey W j Z) J.outputFieldOrder := by
  obtain ⟨v,cost,owns⟩:=e.forecast
  unfold assay at owns
  refine ⟨v,cost,?_⟩
  intro i F tag W o inside small healthy j Z hj dirs clipped
  have block : (p₀).B = radiusB x₁ := (A.output_norm z.level).block
  have dist := (A.output_norm z.level).distance
  have roof : (p₀).threshold ≤ 2*fiery G x₁ (S₀).patch.L := by
    rw [e.plays.rehearsed.temp_eq]
    exact e.cash.choose.laws.data.room.temperatures
  have geo : coverNumber (radiusB x₁) (Brim.plate e.cash.choose i).support ≤ radiusB x₁ := by
    rw [← block]; exact small
  exact owns _ _ (S₀) (T₀) rfl (atBudget (Y₁) (p₁)) _ e.cash.choose F i W tag (p₀)
    block dist e.plays o inside geo healthy j Z hj dirs
    (fun a=>Brim.pacing (Z a) _ (clipped a) _ inside dist (dirs a) _ _ geo roof)

end YM.Integration.WilsonLongContactNearSchedule
