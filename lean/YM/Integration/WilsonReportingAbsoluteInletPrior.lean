import YM.Integration.WilsonReportingAbsoluteInletSimultaneous
import YM.Integration.WilsonPhysicalHistoryPriorSelection

/-! Co-elect the original logarithmic aperture with the funding, field station
and absolute thermal reporter on the same physical root system. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletPrior
open Function Lattice RG Wilson RG.Supply Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonWindowJointPurchase WilsonFundedWindowMenu
open WilsonReportingAbsoluteInletSimultaneous
universe u
variable {G : Gauge}

def Menu (hG : G.Simple) (φ : ℕ → ℕ) : Prediction G :=
  @WilsonWindowBookPurchase.Held G φ hG (WilsonPhysicalHistoryPriorAperture.law G φ)

theorem credit (hG : G.Simple) (φ : ℕ → ℕ) : AllPrices (@Menu G hG φ) := fun s M =>
  from_guard (WilsonWindowBookPurchase.prepaid hG _ s (ThroughLaunch.raging s M)
    (WilsonPhysicalHistoryPriorSelection.permitted φ s (ThroughLaunch.raging s M)))

theorem on_run (hG : G.Simple) (φ : ℕ → ℕ) (R : Run G) (purchased : Menu hG φ R.kit) :
    WilsonPhysicalHistoryPriorAperture.Paid R.rolls (roots hG R.metals.p R.metals.K) φ R.alloy.delay := by
  obtain ⟨_,_,_,_,_,_,_,_,dated⟩ := purchased
  exact dated

theorem original (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (φ : ℕ → ℕ) (p : Prediction G) (paid : AllPrices (@p)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      (∀ j, cap j ≤ (R.metals.p.profile j).order) ∧ p R.kit ∧ StationInvoice R ∧
      WilsonPhysicalHistoryPriorAperture.Paid R.rolls (roots hG R.metals.p R.metals.K) φ R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      WilsonWindowReportingPace.Slow R.kit ∧ ∃ Θ v,
        (CustodyR.minted G).items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Campaign.Sky R T Θ v ∧
        WilsonReportingAbsoluteInletLiveRun.PanelDates R ∧ WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price ∧
        AllAnchors R Θ.price := by
  obtain ⟨R,T,W,tall,⟨other,bill⟩,station,continuum,original,slow,table⟩ :=
    WilsonReportingAbsoluteInletSimultaneous.original.{u} cap mono hG hε
      (@Together G (@p) (@Menu G hG φ)) (fun s M => joint (paid s M) (credit hG φ s M))
  exact ⟨R,T,W,tall,other,station,on_run hG φ R bill,continuum,original,slow,table⟩

end YM.Integration.WilsonReportingAbsoluteInletPrior
