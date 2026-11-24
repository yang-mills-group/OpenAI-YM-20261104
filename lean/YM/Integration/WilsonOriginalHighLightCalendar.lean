import YM.Integration.WilsonOriginalHighLightRun
import YM.Integration.QLocalRequestedSectorCalendar

/-! The fixed marked local booking and the original physical comparison on the high-wage factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalHighLightCalendar

open Filter RG RG.Supply Precision Org Push.PriceCompiler Lattice
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection

universe u
variable {G : Gauge}

open WilsonOriginalMarkedExistence
open FullQLocal.RenderedStep
variable {V : Type}

theorem selected (slow : ℝ → ℝ) (movable : Stationary.Movable slow) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (J : Request V) (Δ : Decal G) (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      QLocalRequestedSectorCalendar.Paid J Δ extra γ R.kit ∧
      WilsonOriginalHighSelection.Salary G R.kit ∧ Stationary.LightPath R.alloy.B.kin slow ∧
      Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧ Charged R :=
  WilsonOriginalHighLightRun.selectedWith.{u} movable hG hε
    (@QLocalRequestedSectorCalendar.Paid G V J Δ extra γ)
    (fun s t => QLocalRequestedSectorCalendar.prepaid J Δ extra γ hG hγ s (ThroughLaunch.raging s t))

end YM.Integration.WilsonOriginalHighLightCalendar
end
