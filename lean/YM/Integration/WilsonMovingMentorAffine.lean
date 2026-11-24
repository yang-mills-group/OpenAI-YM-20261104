import YM.Integration.WilsonMovingMentorPortfolio
import YM.Integration.WilsonRootedHeldAffineWallet

/-! The same Wilson course prepays the genuine held-forest tariff at every
stage of the selected physical register. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorAffine
universe u
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
open WilsonLimitConstruction WilsonLimitConstruction.FundedPredictionSupply WilsonGaussianDeterminantTender
open PhysicalNext.Repeat.Daisy.Charity.RG12 WilsonLimitConstruction.FundedCompanySelection
open WilsonOriginalMarkedExistence GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonMovingCourseElection (Course)
theorem original (ask : WilsonMovingShadowPrices.Ask) {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi) (δ : Charity.RG12.Decal G)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ)
    (ρ : WilsonLongContactSectorProtection.Premium G J.outputFieldOrder)
    (grant : WilsonLongContactSectorProtection.Admitted J ρ)
    (other rider : Prediction G) (funds : FundedPredictionSupply.AllPrices (@other))
    (ticket : WilsonMovingMentorOwnership.AllPrices ask Real.log
      (@WilsonMovingStoredFactor.OnMenu G (@rider))) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
      (affine : ManuscriptQLocalCofinalAffineFields.Paid R)
      (paid : QLocalRequestedSectorCalendar.Paid J (joined G J χ δ) extra γ R.kit),
      Course.{u} ask hG ε J extra γ ManuscriptQLocalCofinalAffineFields.schedule R T W affine.1 ∧
      ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧
      (∀ through, ∃ first, WilsonRootedPhysicalSpringAffineRows.After R affine through first) ∧
      WilsonGaussianDeterminantTender.On R J χ δ extra γ paid ∧
      RG01Estimate.Chart.Barrier R.alloy (fun _ _=>1) ∧
      Juniper.Mulberry.Lanterns R.kit.shape R.alloy.delay ∧
      WilsonMovingSensorReserve.Extra R.kit ∧ WilsonVacuumPreResetRenderCalendar.Issued R.kit ∧
      RG01Estimate.Chart.Barrier R.alloy (fun _ i => ((i:ℝ)+1)⁻¹) ∧ WilsonRootedPhysicalBright.Eligible R.kit ∧
      WilsonRootedPhysicalCommonCut.Eligible R.kit ∧ WilsonVacuumPreResetCurvatureReserve.Issued R.kit ∧
      WilsonVacuumPreResetPrecursorReserve.Issued R.kit ∧ WilsonRootedHeldAffineWallet.Eligible R.kit ∧ other R.kit ∧
      Extension.UV.Archive R.alloy.B ∧ (∃ f, RankCovariance.ShapePort R.alloy.B.a R.alloy.B.M f) ∧
      WilsonMovingMentorSalary.Admitted ask R.kit ∧ WilsonMovingMentorPhase.Canonical R.kit ∧
      WilsonLongContactSectorProtection.Paid J (joined G J χ δ) extra γ ρ R.kit ∧ rider R.kit := by
  let held : Prediction G := @Both G (@WilsonRootedHeldAffineWallet.Eligible G) (@other)
  have price : FundedPredictionSupply.AllPrices (@held) := fun s T => FundedPredictionSupply.both
    (WilsonRootedHeldAffineWallet.prepaid (G:=G) s T) (funds s T)
  obtain ⟨R,T,W,affine,paid,physical,jets,fields,det,chart,derivatives,sensor,render,times,
    bright,short,upper,lower,additional,archive,shape,salary,phase,protection,courses⟩ :=
      WilsonMovingMentorPortfolio.original ask hG hε J χ δ extra γ hγ ρ grant (@held) (@rider) price ticket
  exact ⟨R,T,W,affine,paid,physical,jets,fields,det,chart,derivatives,sensor,render,times,
    bright,short,upper,lower,additional.1,additional.2,archive,shape,salary,phase,protection,courses⟩

end YM.Integration.WilsonMovingMentorAffine
end
