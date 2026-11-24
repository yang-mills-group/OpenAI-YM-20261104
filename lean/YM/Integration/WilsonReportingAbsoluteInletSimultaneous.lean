import YM.Integration.WilsonReportingAbsoluteInletFundedRun
import YM.Integration.WilsonReportingAbsoluteInletWholeWord
import YM.Integration.WilsonPositionThermometerStationFunding
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun

/-! A common original existence and inlet purchase, before the input color,
forest, finite accuracy, cutoff and period of either thermal reading. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletSimultaneous
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowJointPurchase WilsonConditionalTaylorLabels
open scoped Classical

universe u
variable {G : Gauge}

def StationInvoice (R : Run G) : Prop :=
  let demand := fun (s : Sheet G) (_ : MapPrices) => NativeComponentRecipe.Choice s
  R2I.RG05Joint.PostnumericPreselection demand
    (WilsonPositionThermometerStationFunding.combined demand NativeComponentRecipe.floor)
    NativeComponentRecipe.numeric ActualRunNativeComponentRecipe.postnumeric R

def AllAnchors (R : Run G) (κ : ℝ) : Prop :=
  ∀ {c : ℝ}, 1 < c → ∀ (P q : ℕ) (b : Roster G) (h : ℕ → ℕ → ℕ → ℝ),
    WilsonReportingAbsoluteInletNativeInvoice.InversePrice R (WilsonReportingAbsoluteInletCaptured.rank κ P q b) h →
    WilsonReportingAbsoluteInletWholeWord.Receipt R c P q b h

theorem original (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (p : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@p)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      (∀ j, cap j ≤ (R.metals.p.profile j).order) ∧ p R.kit ∧ StationInvoice R ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      WilsonWindowReportingPace.Slow R.kit ∧ ∃ Θ v,
        (CustodyR.minted G).items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Campaign.Sky R T Θ v ∧
        WilsonReportingAbsoluteInletLiveRun.PanelDates R ∧ WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price ∧
        AllAnchors R Θ.price := by
  let demand := fun (s : Sheet G) (_ : MapPrices) => NativeComponentRecipe.Choice s
  have hTrue : R2I.EventuallyPaid (fun _ : Levels G => True) :=
    fun _ _ _ delay => ⟨delay, DelayLe.refl _, by intros; trivial⟩
  obtain ⟨R,T,tall,bill,penalty,station,orders,windows,treasury,period,⟨W⟩,funded,
    _,readout,slow,Θ,v,custody,sky,dates,report⟩ :=
    R2I.RG05Joint.selectRunWithAbsoluteMarkedForecast cap mono (Λ := NativeFVAPlateau.Funded)
      (RiderResourceDynamics.defaultDynamics G).cultivate (CustodyR.minted G) (garment10 G)
      ε hε hG hTrue (fun _ _ h => h) demand (fun s _ => NativeComponentRecipe.available hG s)
      (WilsonPositionThermometerStationFunding.combined demand NativeComponentRecipe.floor)
      NativeComponentRecipe.numeric ActualRunNativeComponentRecipe.postnumeric (@p) credit
  have selection := WilsonPositionThermometerStationFunding.previous demand NativeComponentRecipe.floor
    NativeComponentRecipe.numeric ActualRunNativeComponentRecipe.postnumeric R station
  let A : FundedPlateauRun.Purchase (garment10 G) ε
      (fun s (_ : MapPrices) => NativeComponentRecipe.Choice s) NativeComponentRecipe.floor
      NativeComponentRecipe.numeric ActualRunNativeComponentRecipe.postnumeric :=
    ⟨R,T,W,penalty,selection,orders,treasury,period,funded,readout,windows⟩
  have original := fundedOriginalRun_on.{u} hG A.pillars A.penalty A.funded
    (ActualRunNativeComponentRecipe.of_preselection A.run A.selected)
    A.orders A.treasury A.period A.readout
  exact ⟨R,T,W,tall,bill,station,A.correlations hG,original,slow,Θ,v,custody,sky,dates,report,
    fun {_} hc P q b h income => WilsonReportingAbsoluteInletWholeWord.reported sky hG slow.2 slow.1 hc P q b h income⟩

end YM.Integration.WilsonReportingAbsoluteInletSimultaneous
