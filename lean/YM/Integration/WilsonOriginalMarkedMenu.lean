import YM.Integration.WilsonWindowOriginalRun
import YM.Integration.WilsonWindowJointPurchase
import YM.Integration.WilsonOriginalMarkedExistence

/-! The physical menu pays its chosen invoice together with the two original
marked grants. The selected run controls both its charged interaction mass and
connected observables under its actual exterior law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMarkedMenu

open Filter Lattice RG Wilson Marker RG.Supply Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology

universe u v
variable {G : Gauge}

/-- Original charges and the Gibbs cumulant bound for the same local redraw. -/
structure Marked (R : Run G) : Prop where
  marker : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay
  checkoutPaid : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay
  charged : WilsonOriginalMarkedExistence.Charged R
  connected {V : Type v} [Fintype V] [DecidableEq V] {J : Census V}
      (q : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (N p : ℕ) (hm : m < N) (S : Support (R.family.side m p)) (s : J.Mode)
      (F : V → Config G (R.family.side m p) → ℂ) (b : V → ℝ),
      (∀ i, Measurable (F i)) → (∀ i, 0 ≤ b i) → (∀ i U, ‖F i U‖ ≤ b i) →
      ‖WilsonTagCumulantRate.coefficient s (ActualRunCoarseReadout.expectation R N p m) F -
        WilsonTagCumulantRate.coefficient s (OriginalMarkedGibbsCumulant.refill R (p:=p) (d:=q+1) hm S) F‖ ≤
        δ * S.card * (Pert.Asymptotics.regulatorRun R.family N p (m+1))^(q+1) *
          WilsonTagCumulantRate.slope s b

/-- The supplied physical invoice and both original marked grants belong to the selected factor. -/
theorem selectedWith (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (prediction : Prediction G) (paid : WilsonFundedWindowMenu.AllPrices (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      prediction R.kit ∧ Marked.{v} R ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W := by
  obtain ⟨R, T, W, both, correlations, funded⟩ :=
    WilsonWindowOriginalRun.select.{u} hG hε
      (@WilsonWindowJointPurchase.Together G (@prediction) (@WilsonOldActionForecast.Eligible G))
      (fun s t => WilsonWindowJointPurchase.joint (paid s t) (WilsonOldActionForecast.allPrices s t))
  obtain ⟨marker, fee⟩ := WilsonOldActionForecast.issued R both.2
  refine ⟨R, T, W, both.1, ⟨marker, fee, OriginalMarkedGibbsRate.charged R hG, ?_⟩, correlations, funded⟩
  intro V _ _ J q δ hδ
  exact OriginalMarkedGibbsRate.purchased (J:=J) R hG marker fee q δ hδ

/-- The concrete physical inputs and their original UV archive have a paid menu at every sheet. -/
theorem physicalArchive (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      (WilsonFundedWindowCompany.PhysicalInputs R.kit ∧ Extension.UV.Archive R.alloy.B) ∧
      Marked.{v} R ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W :=
  selectedWith.{u,v} hG hε (@WilsonWindowOriginalRun.ArchivedInputs G)
    (fun s t => WilsonWindowOriginalRun.archive_paid s (ThroughLaunch.raging s t))

end YM.Integration.WilsonOriginalMarkedMenu
end
