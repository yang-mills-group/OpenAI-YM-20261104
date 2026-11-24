import YM.Integration.WilsonMovingCommonSelection
import YM.Integration.WilsonMovingCommonForecasts
import YM.Integration.WilsonMovingPhysicalFoundation
import YM.Integration.WilsonMovingTrebleMargin

/-! All original campaign and scalar-source choices with the additional old singleton quotation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingCourseElection
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical

open RGLocalTaylor RGLocalTaylor.Laminate

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}

universe u
open WilsonLimitConstruction WilsonLimitConstruction.FundedPredictionSupply WilsonGaussianDeterminantTender

open PhysicalNext.Repeat.Daisy.Charity.RG12 WilsonLimitConstruction.FundedCompanySelection
open WilsonOriginalMarkedExistence GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
structure Course (ask : WilsonMovingShadowPrices.Ask) [Fintype V] (hG : G.Simple) (ε : ℝ) (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (order : ℕ → ℕ → ℕ) (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
    (paid : ManuscriptQLocalScalarSourcePurchase.Paid order R.kit) : Prop where
  calendar : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit
  orders : ∀ i, i ≤ (R.metals.p.profile i).order ∧ i ≤ (R.metals.p.profile i).power
  spring : R2I.Funded ((Mallow.orbitD G).paired (garment10 G)) R T
  height : Mallow.RG12.Earned (ManuscriptQLocalMarkedHeightRun.acquisition G J) R.kit.shape R.alloy.delay
  quotation : WilsonMovingCommonPrices.Stored ask R.kit
  width : WilsonMovingTrebleMargin.Wider 4 R.kit
  light : Stationary.LightPath R.alloy.B.kin Real.log
  marker : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay
  checkout : Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay
  correlations : NativeFVAPlateau.Correlations R
  original : FundedOriginalProperties.{u} hG ε W
  charged : Charged R
  gaussian : ∀ {I : Type} [DecidableEq I] {Γ : Marker.Census I} (d : LocalFormal.Datum R.family Γ),
    WilsonRootedPhysicalSpringGaussian.Gaussian R d order paid

/-- Any genuinely purchased canonical-menu claim meets both original scalar calendars on the same run. -/
theorem original (ask : WilsonMovingShadowPrices.Ask) {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi) (δ : Charity.RG12.Decal G)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ)
    (other rider : Prediction G) (funds : FundedPredictionSupply.AllPrices (@other))
    (ticket : WilsonMovingCommonPrices.AllPrices ask Real.log (@WilsonMovingStoredFactor.OnMenu G (@rider))) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
      (affine : ManuscriptQLocalCofinalAffineFields.Paid R)
      (paid : QLocalRequestedSectorCalendar.Paid J (joined G J χ δ) extra γ R.kit),
      Course.{u} ask hG ε J extra γ ManuscriptQLocalCofinalAffineFields.schedule R T W affine.1 ∧
      ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧
      (∀ through, ∃ first, WilsonRootedPhysicalSpringAffineRows.After R affine through first) ∧
      WilsonGaussianDeterminantTender.On R J χ δ extra γ paid ∧
      RG01Estimate.Chart.Barrier R.alloy (fun _ _=>1) ∧
      Juniper.Mulberry.Lanterns R.kit.shape R.alloy.delay ∧
      WilsonMovingSensorReserve.Extra R.kit ∧ other R.kit ∧ rider R.kit := by
  let Δ:=WilsonGaussianDeterminantTender.joined G J χ δ
  let old:=@QLocalRequestedSectorCalendar.Paid G V J Δ extra γ
  let barrier:=@WilsonMovingChartReserve.Eligible G (fun _ _=>1)
  let next:=@Both G (@WilsonMovingLogForecast.Eligible G) (@Both G (@WilsonMovingSensorReserve.Extra G) (@other))
  let all:=@Both G (@old) (@Both G (@barrier) (@next))
  have pay:FundedPredictionSupply.AllPrices (@all):=by
    intro s t
    exact both (QLocalRequestedSectorCalendar.prepaid J Δ extra γ hG hγ s (ThroughLaunch.raging s t))
      (both (WilsonMovingChartReserve.prepaid (G:=G) (fun _ _=>1) (fun _ _ _=>zero_lt_one) s t)
        (both (WilsonMovingLogForecast.prepaid s t) (both (WilsonMovingSensorReserve.prepaid s t) (funds s t))))

  let order := ManuscriptQLocalCofinalAffineFields.schedule
  let scalar := @Both G (@ManuscriptQLocalScalarSourcePurchase.Paid G order)
    (@ManuscriptQLocalScalarClockPurchase.Paid G order)
  let register := @Both G (@QLocalRequestedSectorCalendar.Paid G V J (WilsonRootedJointCalendar.scheme G J) extra γ)
    (@Both G (@WilsonOldActionForecast.Eligible G) (@WilsonMovingTrebleMargin.Wider G 4))
  let stock := @Both G (@all) (@Both G (@scalar) (@register))
  have stockPrice : FundedPredictionSupply.AllPrices (@stock) := by
    intro s t
    exact both (pay s t) (both
      (both (ManuscriptQLocalScalarSourcePurchase.prepaid order s (ThroughLaunch.raging s t))
        (ManuscriptQLocalScalarClockPurchase.prepaid order s (ThroughLaunch.raging s t)))
      (both (QLocalRequestedSectorCalendar.prepaid J (WilsonRootedJointCalendar.scheme G J) extra γ hG hγ s (ThroughLaunch.raging s t))
        (both (WilsonOriginalMarkedExistence.prepaid s (ThroughLaunch.raging s t))
          (WilsonMovingTrebleMargin.prepaid 4 s t))))
  let funded := @Both G (@WilsonMovingCommonPrices.Stored G ask)
    (@Both G (@WilsonOriginalLightSelection.Lit G Real.log) (@stock))
  obtain ⟨R,T,W,h,orders,spring,height,corr,prior⟩ :=
    WilsonMovingPhysicalFoundation.purchased.{u} ask J hG hε (@Both G (@funded) (@rider))
      (WilsonMovingCommonForecasts.together ask Real.log
        (WilsonMovingStoredFactor.ordinary ask Real.log stockPrice) ticket)
  obtain ⟨⟨quotation,light,book,affine,calendar,eligible,width⟩,ride⟩ := h
  obtain ⟨marker,checkout⟩ := WilsonOldActionForecast.issued R eligible
  exact ⟨R,T,W,affine,book.1,
    ⟨calendar,orders,spring,height,quotation,width,light,marker,checkout,corr,prior,
      OriginalMarkedGibbsRate.charged R hG,fun d => ManuscriptQLocalGaussianRootPrice.original R d affine.1⟩,
    ManuscriptQLocalScalarProgramSelection.measuredOn R,WilsonRootedPhysicalSpringAffineRows.window R affine,
    WilsonGaussianDeterminantTender.opens R J χ δ extra γ book.1 hG,book.2.1,book.2.2.1,
    book.2.2.2.1,book.2.2.2.2,ride⟩

end YM.Integration.WilsonMovingCourseElection
end
