import YM.Integration.WilsonOriginalHighPostnumericRun
import YM.Integration.WilsonOriginalMarkedExistence

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPlateauRun

open Filter Lattice RG RG.Supply Precision
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12

universe v
variable {G : Gauge}

theorem purchaseHigh (hG : G.Simple) (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (Demand : Sheet G → MapPrices → Type v) (available : ∀ s q, Nonempty (Demand s q))
    (extra : ∀ s q, Demand s q → ℕ → ℕ)
    (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
    (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : YM.Integration.WilsonOriginalHighSelection.AllPrices (@prediction)) :
    ∃ A : Purchase Δ ε Demand extra numeric postnumeric, prediction A.run.kit := by
  have hTrue : R2I.EventuallyPaid (fun _ : Levels G => True) :=
    fun _ _ _ V => ⟨V, Push.PriceCompiler.DelayLe.refl _, by intros; trivial⟩
  obtain ⟨R, T, hPrediction, hpenalty, hselected, horders, hWindows, hTreasury,
      hPeriod, ⟨W⟩, hFunded, _, hReadout, _⟩ :=
    R2I.RG05Joint.postnumericRunWithHighPocket
      (Λ := NativeFVAPlateau.Funded) (RiderResourceDynamics.defaultDynamics G).cultivate
      (CustodyR.minted G) Δ ε hε hG hTrue (fun _ _ h => h)
      Demand available extra numeric postnumeric (@prediction) paid
  exact ⟨⟨R, T, W, hpenalty, hselected, horders, hTreasury, hPeriod, hFunded,
    hReadout, hWindows⟩, hPrediction⟩

end YM.Integration.WilsonLimitConstruction.FundedPlateauRun
end

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonLimitConstruction

open Filter Lattice PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12
open scoped BigOperators Topology

universe u

theorem fundedHighRun_with_prediction
    {G : Gauge} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : YM.Integration.WilsonOriginalHighSelection.AllPrices (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      prediction R.kit ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W := by
  obtain ⟨A, hPrediction⟩ := FundedPlateauRun.purchaseHigh hG (garment10 G) hε
    (fun s (_ : Precision.MapPrices) => NativeComponentRecipe.Choice s)
    (fun s _ => NativeComponentRecipe.available hG s)
    NativeComponentRecipe.floor NativeComponentRecipe.numeric
    ActualRunNativeComponentRecipe.postnumeric (@prediction) paid
  exact ⟨A.run, A.campaign, A.pillars, hPrediction, A.correlations hG,
    fundedOriginalRun_on.{u} hG A.pillars A.penalty A.funded
      (ActualRunNativeComponentRecipe.of_preselection A.run A.selected)
      A.orders A.treasury A.period A.readout⟩

end YM.Integration.WilsonLimitConstruction
end

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalHighRun

open Filter RG RG.Supply Precision Org Push.PriceCompiler Lattice
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection

universe u
variable {G : Gauge}

open WilsonOriginalMarkedExistence
theorem selectedWith (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (prediction : Prediction G) (price : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      prediction R.kit ∧ WilsonOriginalHighSelection.Salary G R.kit ∧
      Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧ Charged R := by
  obtain ⟨R, T, W, predicted, correlations, original⟩ :=
    fundedHighRun_with_prediction.{u} hG hε
      (@FundedPredictionSupply.Both G (@FundedPredictionSupply.Both G (@prediction) (@WilsonOldActionForecast.Eligible G))
        (@WilsonOriginalHighSelection.Salary G))
      (fun s t => WilsonOriginalHighSelection.ordinary
        (FundedPredictionSupply.both (price s t) (WilsonOriginalMarkedExistence.prepaid s (ThroughLaunch.raging s t))))
  obtain ⟨marker, checkout⟩ := WilsonOldActionForecast.issued R predicted.1.2
  exact ⟨R, T, W, predicted.1.1, predicted.2, marker, checkout, correlations, original,
    OriginalMarkedGibbsRate.charged R hG⟩

end YM.Integration.WilsonOriginalHighRun
end
