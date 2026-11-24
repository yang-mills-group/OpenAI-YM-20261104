import YM.Integration.WilsonLimitConstruction.FundedOrdinaryReentry
import YM.Integration.WilsonPreparedDualPrice

/-! Ordinary-event funding on the true zero-calibration initial Wilson inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInitialOrdinaryPrice
open Filter Lattice Wilson RG Marker PhysicalNext.Repeat.Legato IterationFour
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Pert.Asymptotics MergeProof MergeProof.Accent IterationFour.Vacuum PhysicalNext.ThroughLaunch
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}

/-- Zero calibration without an incoming regular remainder immediately buys
the original unit ordinary rate uniformly before every cutoff and period. -/
theorem funded (R : Run G) (hG : G.Simple) (J : Request V) (A : NumericSchedule R.family J) (K : NumericPrices A) :
    ∀ᶠ m : ℕ in atTop, ∀ d : LocalFormal.Datum R.family Γ, d.level=m →
      ∀ (F : AnalyticInput J A d) (I : FullPreparedInputAt F 0), I.regularPrice=0 → Retained.ordinaryRate K I 1 ≤1 := by
  let eta := fun (_ _ _ : ℕ) => (0:ℝ)
  have hη : Retained.UniformlyFlat (C:=R.family) J eta := by
    constructor
    · intros; exact le_rfl
    · intro q
      refine ⟨0,?_⟩
      intros
      exact pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) q
  filter_upwards [WilsonLimitConstruction.FundedOrdinaryReentry.step (Γ:=Γ) R hG J A K eta hη 0] with m gold
  intro d hd F I hr
  apply (gold d hd F I _).1
  rw [hr]
  exact Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _

variable [Nonempty V] {B : MS.Local.Physical.Deck G}
    (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B) (J : Request V) (A : NumericSchedule R.family J)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A

/-- Direct actual prepared-data version of the original ordinary price. -/
theorem prepared (K : NumericPrices (A₀)) (Q : MS.Land.Prescription B) (μ : ℝ)
    (hStage : WithStage R.metals.p OriginalRunConstruction.originalOrders) :
    ∀ᶠ m : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.level=m →
      ∀ (o : V → Site (R.family.side (d.level+1) d.period)) (orders : V → ℕ)
        (hm : ActualOriginalQInitialPreparation.start R hG u J A hStage ≤ d.level)
        (hp : (J₀).physicalPeriodLower ≤ (R.family.S.period d.period).val) (top : d.cutoff=d.level+1) (T : Campaign R),
      Retained.ordinaryRate K (ActualOriginalQInitialPreparation.prepared R hG u J A d Q o μ orders hStage hm hp top T) 1 ≤ 1 := by
  filter_upwards [funded (Γ:=Stock.census V) R hG (J₀) (A₀) K] with m h
  intro d hd o orders hm hp top T
  exact h d hd _ _ (ActualOriginalQInitialPreparation.prepared_fields R hG u J A d Q o μ orders hStage hm hp top T).2.2.1

end YM.Integration.WilsonInitialOrdinaryPrice
