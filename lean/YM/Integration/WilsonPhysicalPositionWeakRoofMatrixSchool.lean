import YM.Integration.WilsonPhysicalPositionWeakRoofMatrixDates
import YM.Integration.WilsonThermometerOrdinarySchool
import YM.Integration.WilsonThermometerOrdinarySelection
import YM.Integration.WilsonReportingAbsoluteInletSchool

/-! The original graded school, its actual thermal campaign and both weak-panel calendars on one named Wilson hierarchy. -/
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

theorem withRoofedMatrix (ν:Side→ℕ→ℕ→ℝ) (positive:∀ L j d,0<ν L j d) (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    {claim:Prediction G} (supply:WilsonMatrixTicketLengthsLender.Supply G (@claim))
    (p : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@p)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T), R2I.RG05Joint.ReporterRoofs.Admitted ν R ∧
      (∀ j, cap j ≤ (R.metals.p.profile j).order) ∧ (claim R.kit ∧ p R.kit) ∧ StationInvoice R ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      WilsonWindowReportingPace.Slow R.kit ∧ ∃ Θ v,
        (CustodyR.minted G).items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Campaign.Sky R T Θ v ∧
        WilsonReportingAbsoluteInletLiveRun.OrdinaryDates R ∧ WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price ∧
        AllAnchors R Θ.price := by
  let demand := fun (s : Sheet G) (_ : MapPrices) => NativeComponentRecipe.Choice s
  have hTrue : R2I.EventuallyPaid (fun _ : Levels G => True) :=
    fun _ _ _ delay => ⟨delay, DelayLe.refl _, by intros; trivial⟩
  obtain ⟨R,T,roof,tall,bill,penalty,station,orders,windows,treasury,period,⟨W⟩,funded,
    _,readout,slow,Θ,v,custody,sky,dates⟩ :=
    R2I.RG05Joint.ReporterRoofs.dates ν positive cap mono (Λ := NativeFVAPlateau.Funded)
      (RiderResourceDynamics.defaultDynamics G).cultivate (CustodyR.minted G) (garment10 G)
      ε hε hG hTrue (fun _ _ h => h) demand (fun s _ => NativeComponentRecipe.available hG s)
      (WilsonPositionThermometerStationFunding.combined demand NativeComponentRecipe.floor)
      NativeComponentRecipe.numeric ActualRunNativeComponentRecipe.postnumeric supply (@p) credit
  have report : WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price := by
    intro c hc P q roster forecast income δ hd
    exact WilsonReportingAbsoluteInletCaptured.roster sky hG slow.2 slow.1 hc P q roster forecast income hd
  have selection := WilsonPositionThermometerStationFunding.previous demand NativeComponentRecipe.floor
    NativeComponentRecipe.numeric ActualRunNativeComponentRecipe.postnumeric R station
  let A : FundedPlateauRun.Purchase (garment10 G) ε
      (fun s (_ : MapPrices) => NativeComponentRecipe.Choice s) NativeComponentRecipe.floor
      NativeComponentRecipe.numeric ActualRunNativeComponentRecipe.postnumeric :=
    ⟨R,T,W,penalty,selection,orders,treasury,period,funded,readout,windows⟩
  have original := fundedOriginalRun_on.{u} hG A.pillars A.penalty A.funded
    (ActualRunNativeComponentRecipe.of_preselection A.run A.selected)
    A.orders A.treasury A.period A.readout
  exact ⟨R,T,W,roof,tall,bill,station,A.correlations hG,original,slow,Θ,v,custody,sky,dates,report,
    fun {_} hc P q b h income => WilsonReportingAbsoluteInletWholeWord.reported sky hG slow.2 slow.1 hc P q b h income⟩

end YM.Integration.WilsonReportingAbsoluteInletSimultaneous
end

noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletPrior
open Function Lattice RG Wilson RG.Supply Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonWindowJointPurchase WilsonFundedWindowMenu
open WilsonReportingAbsoluteInletSimultaneous
universe u
variable {G : Gauge}

theorem withRoofedMatrix (ν:Side→ℕ→ℕ→ℝ) (positive:∀ L j d,0<ν L j d) (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    {claim:Prediction G} (supply:WilsonMatrixTicketLengthsLender.Supply G (@claim))
    (φ : ℕ → ℕ) (p : Prediction G) (paid : AllPrices (@p)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T), R2I.RG05Joint.ReporterRoofs.Admitted ν R ∧
      (∀ j, cap j ≤ (R.metals.p.profile j).order) ∧ (claim R.kit ∧ p R.kit) ∧ StationInvoice R ∧
      WilsonPhysicalHistoryPriorAperture.Paid R.rolls (roots hG R.metals.p R.metals.K) φ R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      WilsonWindowReportingPace.Slow R.kit ∧ ∃ Θ v,
        (CustodyR.minted G).items R.alloy.post R.y R.w Θ R.family.path.levels ∧ Campaign.Sky R T Θ v ∧
        WilsonReportingAbsoluteInletLiveRun.OrdinaryDates R ∧ WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price ∧
        AllAnchors R Θ.price := by
  obtain ⟨R,T,W,roof,tall,⟨licensed,other,bill⟩,station,continuum,original,slow,table⟩ :=
    WilsonReportingAbsoluteInletSimultaneous.withRoofedMatrix.{u} ν positive cap mono hG hε supply
      (@Together G (@p) (@Menu G hG φ)) (fun s M => joint (paid s M) (credit hG φ s M))
  exact ⟨R,T,W,roof,tall,⟨licensed,other⟩,station,on_run hG φ R bill,continuum,original,slow,table⟩

end YM.Integration.WilsonReportingAbsoluteInletPrior
end

noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletPhysicalSchool
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowRootPurchase WilsonWindowJointPurchase WilsonWindowBookPurchase WilsonWindowUniversalSchool
open WilsonReportingAbsoluteInletSimultaneous
open scoped Classical
universe u
variable {G : Gauge} {φ : ℕ → ℕ}

theorem withRoofedMatrix (ν:Side→ℕ→ℕ→ℝ) (positive:∀ L j d,0<ν L j d) (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    {claim:Prediction G} (supply:WilsonMatrixTicketLengthsLender.Supply G (@claim))
    (C : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ)
    (external : ∀ (s : Sheet G) (M : MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (U : ℕ → ℕ) (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T), R2I.RG05Joint.ReporterRoofs.Admitted ν R ∧
      (∀ j, cap j ≤ (R.metals.p.profile j).order) ∧ (claim R.kit ∧ more R.kit) ∧ StationInvoice R ∧
      WilsonWindowOriginalHardRadius.Booked R.kit ∧
      (∃ B F, Treehouse.VariableHouse R (roots hG R.metals.p R.metals.K) (rollTab hG R.metals R.rolls)
        C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p)) ∧
      WilsonPhysicalHistoryPriorAperture.Paid R.rolls (roots hG R.metals.p R.metals.K) φ R.alloy.delay ∧
      WilsonWindowReportingPace.Slow R.kit ∧ WilsonWindowOriginalRun.ArchivedInputs R.kit ∧
      WilsonWindowFormalPurchase.Canonical U R.kit ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{u} hG ε W ∧
      Citizen R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      OPE.Log.LogPackage R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors ∧
      ∃ Θ v, (CustodyR.minted G).items R.alloy.post R.y R.w Θ R.family.path.levels ∧
        Campaign.Sky R T Θ v ∧ WilsonReportingAbsoluteInletLiveRun.OrdinaryDates R ∧
        WilsonReportingAbsoluteInletFundedRun.Reported R Θ.price ∧
        AllAnchors R Θ.price := by
  let law := Tracks.vine (flow C) split
  let p : Prediction G := @Together G (@Together G (@more) (@WilsonWindowOriginalHardRadius.Booked G))
    (@Together G (@WilsonReportColumnSubsidy.Eligible G) (@WilsonWindowSchoolInvoice.grant G φ hG law U))
  have school := WilsonWindowSchoolInvoice.prepaid hG law U
    (fun s M => WilsonWindowCourseLaws.physical_course split (external s M))
  have paid : WilsonFundedWindowMenu.AllPrices (@p) := fun s M =>
    joint (joint (credit s M) (WilsonWindowOriginalHardRadius.allPrices s M)) (joint (WilsonReportColumnSubsidy.allPrices s M) (school s M))
  obtain ⟨R,T,W,roof,tall,⟨licensed,⟨outside,hard⟩,subsidy,booked⟩,station,aperture,correlations,original,_,Θ,v,custody,sky,dates,report,anchors⟩ :=
    WilsonReportingAbsoluteInletPrior.withRoofedMatrix.{u} ν positive cap mono hG hε supply φ (@p) paid
  obtain ⟨⟨B,chamber⟩,admit,pace,archive,formal⟩ := WilsonWindowSchoolInvoice.on_run hG R law U booked
  obtain ⟨F,house_paid⟩ := house hG R _ _ C B split chamber admit
  obtain ⟨citizen,logBook⟩ := WilsonReportCitizenRun.on_run.{u} hG W original subsidy
  exact ⟨R,T,W,roof,tall,⟨licensed,outside⟩,station,hard,⟨B,F,house_paid⟩,aperture,pace,archive,formal,correlations,
    original,citizen,logBook,Θ,v,custody,sky,dates,report,anchors⟩

end YM.Integration.WilsonReportingAbsoluteInletPhysicalSchool
end

noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletSchool

open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open MSbar.Heath WilsonWindowRootPurchase WilsonWindowJointPurchase
open WilsonWindowBookPurchase WilsonWindowUniversalSchool
open WilsonReportingAbsoluteInletForecastMarket WilsonReportingAbsoluteInletForecastElection
open Pert.Asymptotics FormalBulk08 FormalBulk08.Flat FormalBulk08.Series FormalBulk08.Wine
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal
open WilsonConditionalTaylorLabels WilsonConditionalTaylorCourseAttachment WilsonReportingAbsoluteInletForecastBooks
open WilsonReportingAbsoluteInletSimultaneous
open scoped BigOperators Classical

universe u
variable {G : Gauge} {φ : ℕ → ℕ}

/-- The material books, physical hierarchy and both thermal estimates on one campaign. -/

theorem withRoofedMatrixSelected (ν:Side→ℕ→ℕ→ℝ) (positive:∀ L j d,0<ν L j d) (cap : ℕ → ℕ) (mono : Monotone cap) (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    {claim:Prediction G} (supply:WilsonMatrixTicketLengthsLender.Supply G (@claim))
    (V : Voice G) (clear : Clear G V) (C : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ)
    (external : ∀ (s : Sheet G) (M : MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (U : ℕ → ℕ) (more : Prediction G) (credit : WilsonFundedWindowMenu.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T), R2I.RG05Joint.ReporterRoofs.Admitted ν R ∧
      claim R.kit ∧ R2I.RG05Joint.AcrossPanels R.kit ∧ OnRun.{u} cap hG ε C U (@more) R T W := by
  classical
  let us := (Finset.univ : Finset G.ColorIndex).toList
  let offers : G.ColorIndex → Prediction G := fun a => @Terms G a V
  have sold (a : G.ColorIndex) : WilsonFundedWindowMenu.AllPrices (@offers a) :=
    fun s M => WilsonReportingAbsoluteInletForecastMarket.prepaid hG a V clear s (ThroughLaunch.raging s M)
  obtain ⟨R,T,W,roof,tall,⟨licensed,bill⟩,station,hard,house,aperture,pace,archive,formal,correlations,original,
    citizen,logBook,Θ,v,custody,sky,dates,report,anchors⟩ :=
    WilsonReportingAbsoluteInletPhysicalSchool.withRoofedMatrix.{u} ν positive cap mono hG hε supply C split external U
      (@WilsonReportingAbsoluteInletColorMenu.colors G (@more) (@offers) us)
      (WilsonReportingAbsoluteInletColorMenu.prices (@more) (@offers) credit sold us)
  obtain ⟨outside,remaining⟩ := WilsonReportingAbsoluteInletColorMenu.reads R (@more) (@offers) us bill
  refine ⟨R,T,W,roof,licensed,dates.panels,tall,outside,station,hard,house,aperture,pace,archive,formal,correlations,
    original,citizen,logBook,Θ,v,custody,sky,⟨dates.dates,dates.panels.sky⟩,report,?_⟩
  intro a
  have money : Terms a V R.kit := remaining a (by simp [us])
  exact ⟨on_run R hG a V money report, anchored R hG a V money anchors⟩


end YM.Integration.WilsonReportingAbsoluteInletSchool
end
