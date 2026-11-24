import YM.Integration.WilsonPreparedPointSource
import YM.Integration.WilsonScheduledStartupMoment
import YM.Integration.WilsonModeDual
import YM.Integration.FullQLocalRetainedModelPrice
import YM.Integration.SelectedCofactorPriceReadout

/-! The actual initialized and selected Q source pays an arbitrary native
physical model-defect dual on every field and every allowed torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPreparedDualPrice
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch LocalComparison LocalComparison.Global
open IterationFour IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open MergeProof MergeProof.Accent SelectedWilsonForward
open scoped Classical BigOperators Topology
variable {G : Gauge} {B : MS.Local.Physical.Deck G} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B) (J : Request V) (A : NumericSchedule R.family J)
    (Q : MS.Land.Prescription B) (μ : ℝ) (k : ℕ) (hStage : WithStage R.metals.p OriginalRunConstruction.originalOrders)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A

omit [Nonempty V] in
private theorem normalized (d : LocalFormal.Datum R.family (Stock.census V))
    (o : V → Site (R.family.side (d.level+1) d.period)) (orders : V → ℕ) (i : V) :
    ‖ActualOriginalQInitialInput.scales R hG u J A d Q o μ orders i‖ ≤ 1 := by
  let b := ActualOriginalQInitialInput.normalizer R hG u J A d Q o μ orders
  have hb : 1 ≤ b := le_max_left ..
  change ‖(b:ℂ)⁻¹‖ ≤ 1
  rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans hb)]
  exact inv_le_one_of_one_le₀ hb

/-- The complete signed fine-source cost is polynomial in the reference
inverse coupling uniformly over all original regulators, locations, unit
tests and native price duals. The separate coarse model keeps its actual
retained geometry invoice. -/
theorem selected : ∃ a : ℝ, 0 < a ∧ ∃ q : ℕ, ∀ᶠ m : ℕ in atTop,
    ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.level=m →
    ∀ (o : V → Site (R.family.side (d.level+1) d.period)) (orders : V → ℕ), (∀ i, orders i ≤ k) →
    ∀ (hm : ActualOriginalQInitialPreparation.start R hG u J A hStage ≤ d.level)
      (hp : (J₀).physicalPeriodLower ≤ (R.family.S.period d.period).val) (top : d.cutoff=d.level+1) (T : Campaign R),
    let F := ActualOriginalQInitialPreparation.analyticInput R hG u J A d Q o μ orders hStage hm hp
    let I := ActualOriginalQInitialPreparation.prepared R hG u J A d Q o μ orders hStage hm hp top T
    ∀ {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain R.family.path}
      {K : NumericPrices (A₀)} {M : AnalyticOutput caps Y K F}, ∀ S : Chosen K I M,
    ∀ (x : IndependentTests (J₀).tests) (W : Config G (R.family.side d.level d.period)),
      Poly.price (fun i => F.outputRadii i/F.kernelCosts i) (ActualSelectedModelIntegral.defect S (testInclusion (J₀).tests x) W) ≤ a*R.family.path.levels.clock.hatBeta m^q+
        MarkedPackets.uniformModelCost caps.packetRank (Fintype.card V) (K.geometry d.level) := by
  obtain ⟨b,hb,q,paid⟩ := WilsonScheduledStartupMoment.complete R hG Q u J k μ
  let card := (Fintype.card (Stock.census V).Mode:ℝ)
  have hcard : 0 ≤ card := Nat.cast_nonneg _
  refine ⟨b*(card+1),mul_pos hb (by linarith),q,?_⟩
  filter_upwards [paid,WilsonPreparedPointSource.ready R u] with m hpay href
  intro d e o orders hk hm hp top T
  subst m
  dsimp only
  intro caps Y K M S x W
  let F := ActualOriginalQInitialPreparation.analyticInput R hG u J A d Q o μ orders hStage hm hp
  let c := ActualOriginalQInitialInput.scales R hG u J A d Q o μ orders
  let w (i : V) := F.outputRadii i/F.kernelCosts i
  have hwpos (i : V) : 0<w i := div_pos (F.output_radius_positive i) (F.kernel_positive i)
  let y := ActualSelectedModelIntegral.defect S (testInclusion (J₀).tests x) W
  obtain ⟨L,hl,norming⟩ := SelectedCofactorPriceReadout.norming hwpos y
  have hnorm : ‖L y‖ = Poly.price w y := by rw [norming,Complex.norm_real,Real.norm_of_nonneg (Poly.nonnegative hwpos _)]
  change Poly.price w y ≤ _
  rw [←hnorm]
  change ‖L (ActualSelectedModelIntegral.defect S (testInclusion (J₀).tests x) W)‖ ≤ _
  let ℓ := WilsonModeDual.weights L
  let β := R.family.path.levels.clock.hatBeta d.level
  have he (y : Poly (Stock.census V)) : read ℓ y = L y := (SelectedWilsonForward.value ℓ y).trans (WilsonModeDual.signed L y).symm
  have hd := WilsonPreparedPointSource.selected R hG u J A d Q o μ orders hStage hm hp top T S href ℓ (testInclusion (J₀).tests x) W
  rw [he,he] at hd
  have hwn i : 0 ≤ F.outputRadii i/F.kernelCosts i := div_nonneg (F.output_radius_positive i).le (F.kernel_positive i).le
  have hwu i : F.outputRadii i/F.kernelCosts i ≤ 1 := by
    change ((A₀).radiusLoss d.level)⁻¹/1 ≤ 1
    rw [div_one]
    exact inv_le_one_of_one_le₀ ((A₀).radius_loss_ge_one d.level)
  have hw : (∑ s, ‖ℓ s‖) ≤ card := WilsonModeDual.price hwn hwu L hl
  have H := (hpay d.period o orders hk c (normalized R hG u J A Q μ d o orders) x ℓ).2 W
  rw [hd]
  refine (norm_sub_le ..).trans (add_le_add ?_ ((hl _).trans (S.uniform_model_price x W)))
  have hβ : 0 ≤ β := zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have hA : 0 ≤ b*β^q := mul_nonneg hb.le (pow_nonneg hβ _)
  have av (g : Config G (R.family.side (d.level+1) d.period) → ℂ) :
      actualAverage R.family (N:=d.cutoff) g W = actualAverage R.family (N:=d.level+1) g W :=
    congrArg (fun n : ℕ => actualAverage R.family (N:=n) (p:=d.period) (m:=d.level) g W) top
  calc _ ≤ (b*β^q)*(∑ s, ‖ℓ s‖) := by
         rw [av,congrArg R.family.S.scale top]
         exact H
       _ ≤ (b*β^q)*(card+1) := mul_le_mul_of_nonneg_left (hw.trans (by linarith)) hA
       _ = _ := by dsimp only [β]; ring

end YM.Integration.WilsonPreparedDualPrice
