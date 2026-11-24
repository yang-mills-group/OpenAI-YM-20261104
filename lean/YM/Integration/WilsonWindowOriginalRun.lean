import YM.Integration.WilsonWindowFundedPlateau
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun

/-! Retain a concrete marked-window purchase through the original continuum
campaign. The unconditional instance recovers its real physical input facts. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonWindowOriginalRun

open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12
open WilsonLimitConstruction

universe u

theorem select {G : Gauge} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : WilsonFundedWindowMenu.AllPrices (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      prediction R.kit ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W := by
  obtain ⟨A, bought⟩ := FundedPlateauRun.purchaseAtPhysicalMenu hG (garment10 G) hε
    (fun s (_ : MapPrices) => NativeComponentRecipe.Choice s)
    (fun s _ => NativeComponentRecipe.available hG s)
    NativeComponentRecipe.floor NativeComponentRecipe.numeric
    ActualRunNativeComponentRecipe.postnumeric (@prediction) paid
  exact ⟨A.run, A.campaign, A.pillars, bought, A.correlations hG,
    fundedOriginalRun_on.{u} hG A.pillars A.penalty A.funded
      (ActualRunNativeComponentRecipe.of_preselection A.run A.selected)
      A.orders A.treasury A.period A.readout⟩

theorem physical_inputs_paid {G : Gauge} (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@WilsonFundedWindowCompany.PhysicalInputs G) s price := by
  intro R E flags C z bt
  refine ⟨fun _ => 0, ?_⟩
  intro l hl D w u Z φ S pocket θ p P menu V quarter
  refine ⟨V,DelayLe.refl _,?_⟩
  intro Y hY bar wait hp B archive origins rank
  dsimp only
  intro η q exchange aux rider booth shelter works divides
  exact ⟨flags,pocket⟩

/-- The actual physical choices, moving correlations, and original continuum
and OPE package inhabit the same selected Run. -/
theorem physical_inputs {G : Gauge} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      WilsonFundedWindowCompany.PhysicalInputs R.kit ∧ NativeFVAPlateau.Correlations R ∧
        FundedOriginalProperties.{u} hG ε W :=
  select.{u} hG hε (@WilsonFundedWindowCompany.PhysicalInputs G)
    (fun s T => physical_inputs_paid s (ThroughLaunch.raging s T))

/-- The same selected physical factor keeps its actual pre-merge kinetic
horizons and the startup certificate at every cutoff. -/
def ArchivedInputs {G : Gauge} : FundedCompanySelection.Prediction G := fun {_} {_} {A} F =>
  WilsonFundedWindowCompany.PhysicalInputs F ∧ Extension.UV.Archive A.B

theorem archive_paid {G : Gauge} (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@ArchivedInputs G) s price := by
  intro R E flags C z bt
  refine ⟨fun _ => 0, ?_⟩
  intro l hl D w u Z φ S pocket θ p P menu V quarter
  refine ⟨V,DelayLe.refl _,?_⟩
  intro Y hY bar wait hp B archive origins rank
  dsimp only
  intro η q exchange aux rider booth shelter works divides
  exact ⟨⟨flags,pocket⟩,archive⟩

theorem physical_archive {G : Gauge} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      (WilsonFundedWindowCompany.PhysicalInputs R.kit ∧ Extension.UV.Archive R.alloy.B) ∧
        NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W :=
  select.{u} hG hε (@ArchivedInputs G)
    (fun s T => archive_paid s (ThroughLaunch.raging s T))

end YM.Integration.WilsonWindowOriginalRun
end

