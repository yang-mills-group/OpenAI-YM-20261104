import YM.Integration.WilsonRootedObservedSchedule
import YM.Integration.ActualOriginalQInitialStartup

/-! One selected ultraviolet campaign retains its actual order receipts, its physical
spring purchase and its booked point-source calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedUltravioletElection
open Filter Lattice Wilson RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open FullQLocal FullQLocal.RenderedStep WilsonOriginalMarkedExistence
open scoped Classical Topology
universe u
variable {G : Gauge} {V : Type}

/-- The fixed OPE point labels change the capacity and the test space while the
paid local calendar retains the exact numerical purchase. -/
theorem point [DecidableEq V] [Fintype V] {B : MS.Local.Physical.Deck G} (R : Run G)
    (u : V → MS.Rake.Label B) (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (paid : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit) :
    let J' := ActualOriginalQPointSetup.request R u J
    QLocalRequestedSectorCalendar.Paid J' (WilsonRootedJointCalendar.scheme G J') extra γ R.kit := by
  obtain ⟨book, earlier, windows⟩ := paid
  refine ⟨book, ?_, ?_⟩
  · intro i j step
    have e := earlier i j step
    exact ⟨e.support,e.seam,e.payment⟩
  intro j x hx i stage first
  obtain ⟨w, temp⟩ := windows j x hx i stage first
  exact ⟨⟨⟨w.heir.price⟩,w.ledger,w.captain,w.outer,w.hard,w.analytic,w.glyph⟩,temp⟩

private theorem purchase (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (prediction : Prediction G)
    (price : WilsonOriginalLightSelection.AllPrices Real.log (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T), prediction R.kit ∧
      (∀ i, i ≤ (R.metals.p.profile i).order ∧ i ≤ (R.metals.p.profile i).power) ∧
      R2I.Funded ((Mallow.orbitD G).paired (garment10 G)) R T ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W := by
  obtain ⟨A, hp⟩ := FundedPlateauRun.purchaseHighLight (movable := WilsonOriginalLogLight.movable)
    hG ((Mallow.orbitD G).paired (garment10 G)) hε
    (fun s (_ : Precision.MapPrices) => NativeComponentRecipe.Choice s)
    (fun s _ => NativeComponentRecipe.available hG s) NativeComponentRecipe.floor NativeComponentRecipe.numeric
    ActualRunNativeComponentRecipe.postnumeric (@prediction) price
  have drop : R2I.Funded (garment10 G) A.run A.campaign :=
    { A.funded with localBudget := { A.funded.localBudget with
        tailor := fun j x hx i hi => (A.funded.localBudget.tailor j x hx i hi).2 } }
  exact ⟨A.run, A.campaign, A.pillars, hp, A.orders, A.funded, A.correlations hG,
    fundedOriginalRun_on.{u} hG A.pillars A.penalty drop
      (ActualRunNativeComponentRecipe.of_preselection A.run A.selected)
      A.orders A.treasury A.period A.readout⟩

/-- The physical orbit decal and the original comparison are bought before choosing
point labels, regulator periods, marked tests or local data. -/
theorem selected [Fintype V] (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit ∧
      (∀ i, i ≤ (R.metals.p.profile i).order ∧ i ≤ (R.metals.p.profile i).power) ∧
      R2I.Funded ((Mallow.orbitD G).paired (garment10 G)) R T ∧
      WilsonOriginalHighSelection.Salary G R.kit ∧ Stationary.LightPath R.alloy.B.kin Real.log ∧
      Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧ Charged R := by
  let price := @QLocalRequestedSectorCalendar.Paid G V J (WilsonRootedJointCalendar.scheme G J) extra γ
  obtain ⟨R,T,W,pred,orders,spring,corr,original⟩ := purchase.{u} hG hε
    (@FundedPredictionSupply.Both G (@FundedPredictionSupply.Both G
      (@FundedPredictionSupply.Both G (@price) (@WilsonOldActionForecast.Eligible G))
      (@WilsonOriginalHighSelection.Salary G)) (@WilsonOriginalLightSelection.Lit G Real.log))
    (fun s t => WilsonOriginalLightSelection.ordinary Real.log (WilsonOriginalHighSelection.ordinary
      (FundedPredictionSupply.both (QLocalRequestedSectorCalendar.prepaid J
        (WilsonRootedJointCalendar.scheme G J) extra γ hG hγ s (ThroughLaunch.raging s t))
        (WilsonOriginalMarkedExistence.prepaid s (ThroughLaunch.raging s t)))))
  obtain ⟨marker, checkout⟩ := WilsonOldActionForecast.issued R pred.1.1.2
  exact ⟨R,T,W,pred.1.1.1,orders,spring,pred.1.2,pred.2,marker,checkout,corr,original,
    OriginalMarkedGibbsRate.charged R hG⟩

end YM.Integration.WilsonRootedUltravioletElection
end
