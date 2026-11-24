import YM.Integration.WilsonEmittedMatrixPanelRun
import YM.Integration.WilsonReportingAbsoluteInletSimultaneous
import YM.Integration.WilsonEmittedNestedPurchase
import YM.Integration.WilsonPositionProgramStageInvoice

/-! Original physical funding, the reflected Haar panels, the nested formal block
lengths and the Lodge invoice all hold on one run, before the regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedNestedGround
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowJointPurchase WilsonConditionalTaylorLabels
open scoped Classical

universe u
variable {G : Gauge}

open WilsonReportingAbsoluteInletSimultaneous OPE OPE.Owl
open WilsonMatrixTicketFuelPrice

/-- Both entries describe the block sequence of this actual run. -/
def Schedule (R:Run G) : Prop :=
  WilsonEmittedNestedPurchase.Geometry R.kit ∧ WilsonPositionProgramStageInvoice.Requested R.kit

/-- Reuse the exact original post-election specification. The proof argument
determines its type only. The selected run, campaign, pillars and original
specification in the conclusion are under the same existential quantifier. -/
def Enrolled {claim:∀(R:Run G)(T:Campaign R),Campaign.Pillars R T → Prop}
    (_:∃ (R:Run G) (T:Campaign R) (W:Campaign.Pillars R T),claim R T W) : Prop :=
  ∃ (R:Run G) (T:Campaign R) (W:Campaign.Pillars R T), Schedule R ∧ claim R T W

theorem original (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (p : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@p)) :
    Enrolled (WilsonReportingAbsoluteInletSimultaneous.original.{u} cap mono hG hε (@p) credit) := by
  let demand := fun (s : Sheet G) (_ : MapPrices) => NativeComponentRecipe.Choice s
  have hTrue : R2I.EventuallyPaid (fun _ : Levels G => True) :=
    fun _ _ _ delay => ⟨delay, DelayLe.refl _, by intros; trivial⟩
  let read : Prediction G := @Together G
    (@Together G (@p) (@WilsonPositionProgramStageInvoice.Requested G)) (@WilsonWindowReportingPace.Slow G)
  have charged : WilsonFundedWindowMenu.AllPrices (@read) := fun s M =>
    joint (WilsonPositionProgramStageInvoice.joint hG (credit s M)) (WilsonWindowReportingPace.prepaid hG s _)
  obtain ⟨R,T,tall,⟨⟨nested,⟨⟨bill,stage⟩,slow⟩⟩,panels⟩,penalty,station,orders,
    windows,treasury,period,⟨W⟩,funded,_,readout,Θ,v,custody,sky⟩ :=
    R2I.RG05Joint.selectRunWithPanelMatrix cap mono (Λ := NativeFVAPlateau.Funded)
      (RiderResourceDynamics.defaultDynamics G).cultivate (CustodyR.minted G) (garment10 G)
      ε hε hG hTrue (fun _ _ h => h) demand (fun s _ => NativeComponentRecipe.available hG s)
      (WilsonPositionThermometerStationFunding.combined demand NativeComponentRecipe.floor)
      NativeComponentRecipe.numeric ActualRunNativeComponentRecipe.postnumeric
      (WilsonEmittedNestedPurchase.funded hG (0:Axis)) (@read) charged
  have dates : WilsonReportingAbsoluteInletLiveRun.PanelDates R :=
    ⟨WilsonReportingAbsoluteInletLiveRun.on_run R hG slow,panels⟩
  have report : WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price := by
    intro c hc P q roster forecast income ε₁ ep
    exact WilsonReportingAbsoluteInletCaptured.roster sky hG slow.2 slow.1 hc P q roster forecast income ep
  have selection := WilsonPositionThermometerStationFunding.previous demand NativeComponentRecipe.floor
    NativeComponentRecipe.numeric ActualRunNativeComponentRecipe.postnumeric R station
  let A : FundedPlateauRun.Purchase (garment10 G) ε
      (fun s (_ : MapPrices) => NativeComponentRecipe.Choice s) NativeComponentRecipe.floor
      NativeComponentRecipe.numeric ActualRunNativeComponentRecipe.postnumeric :=
    ⟨R,T,W,penalty,selection,orders,treasury,period,funded,readout,windows⟩
  have original := fundedOriginalRun_on.{u} hG A.pillars A.penalty A.funded
    (ActualRunNativeComponentRecipe.of_preselection A.run A.selected)
    A.orders A.treasury A.period A.readout
  exact ⟨R,T,W,⟨nested,stage⟩,tall,bill,station,A.correlations hG,original,slow,Θ,v,custody,sky,dates,report,
    fun {_} hc P q b h income => WilsonReportingAbsoluteInletWholeWord.reported sky hG slow.2 slow.1 hc P q b h income⟩

end YM.Integration.WilsonEmittedNestedGround
