import YM.Integration.WilsonOriginalMarkedMenu
import YM.Integration.WilsonWindowReportingPace
import YM.Integration.WilsonIncidentRetainedChart

/-! Purchase the reporting pace before selecting the marked original run, and
apply its grants to the true retained chart at every occupied parent. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalIncidentForest

open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open RG.Supply PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open RG16 ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Pert.Asymptotics
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Classical Topology

universe u v
variable {G : Gauge}

/-- The retained fibre uses the actual exterior mass ratio and the original held coarse field. -/
def ForestEstimate (R : Run G) : Prop :=
  ∀ {I : Type} [Fintype I] (J : Voice G), Clear G J →
    ∀ (P : ChartRatio G), LocalRatio P → ∀ {r : ℝ}, 0 < r → r < Chart.small G P →
    ∀ (d : I → ℕ) (q grade : ℕ), q+5 ≤ grade → ∀ {δ : ℝ}, 0 < δ →
    ∀ᶠ j : ℕ in atTop, ∀ N (interior : j+1 < N) per (o : I → Site (R.family.side (j+1) per))
      (T : Forest (R.family.path.levels.clock.op j per).ratio) (V : Config G (R.family.side j per))
      (H : Config G (R.family.side (j+1) per) → ℝ), Envelope H → GaugeInvariant H →
      let Pk := approximation R (p:=per) interior grade
      let B := incident R T d o
      let E := moving T B
      let C := cold R j per d o
      let ν := Measure.pi (fun _ : ({e : T.Free | e ∉ E} : Set T.Free) => G.probHaar)
      let w := WilsonHeldExteriorLaw.weight R N per j V Pk
      let Z := WilsonForestRetainedFibre.mass R (N:=N) T E V
      let retained := ∫ v, Z (R.family.path.rep N per (j+1)) v / Z Pk v *
        (∫ y in ball 0 r, Chart.jacobian P y * C.indicator (fun U => w U * H U)
          (restored T B v (Chart.expLinks G (↥E) y)) ∂Chart.tangent G (↥E)) ∂ν
      |actualAverage R.family (N:=N) (C.indicator H) V - retained| ≤
        δ * regulatorRun R.family N per (j+1)^q * actualAverage R.family (N:=N) (C.indicator (fun U => |H U|)) V

/-- The selected run satisfies the physical and slow-block bounds simultaneously. -/
theorem selectedWith (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (prediction : Prediction G) (paid : WilsonFundedWindowMenu.AllPrices (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      prediction R.kit ∧ WilsonWindowReportingPace.Slow R.kit ∧ WilsonOriginalMarkedMenu.Marked.{v} R ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧ ForestEstimate R := by
  obtain ⟨R, T, W, bought, marked, correlations, funded⟩ :=
    WilsonOriginalMarkedMenu.selectedWith.{u,v} hG hε
      (@WilsonWindowJointPurchase.Together G (@prediction) (@WilsonWindowReportingPace.Slow G))
      (fun s t => WilsonWindowJointPurchase.joint (paid s t)
        (WilsonWindowReportingPace.prepaid hG s (ThroughLaunch.raging s t)))
  obtain ⟨requested, slow⟩ := bought
  refine ⟨R, T, W, requested, slow, marked, correlations, funded, ?_⟩
  intro I _ J clear P hp r pr sr d q grade order δ he
  exact WilsonIncidentRetainedChart.purchased R hG marked.marker marked.checkoutPaid slow.2
    J clear P hp pr sr d q grade order he

/-- The paid physical flags and UV archive give an unconditional original forest estimate. -/
theorem original (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      WilsonWindowOriginalRun.ArchivedInputs R.kit ∧ WilsonWindowReportingPace.Slow R.kit ∧
      WilsonOriginalMarkedMenu.Marked.{v} R ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{u} hG ε W ∧ ForestEstimate R :=
  selectedWith.{u,v} hG hε (@WilsonWindowOriginalRun.ArchivedInputs G)
    (fun s t => WilsonWindowOriginalRun.archive_paid s (ThroughLaunch.raging s t))

end YM.Integration.WilsonOriginalIncidentForest
end
