import YM.Integration.WilsonMovingMentorCurvature
import YM.Integration.WilsonRootedPhysicalCommonCut

/-! The full registered local period cost and both physical stages are purchased on the same course. -/
noncomputable section
namespace YM.Integration.WilsonMovingMentorCommonCut
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
    (other : Prediction G) (funds : FundedPredictionSupply.AllPrices (@other)) :
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
      RG01Estimate.Chart.Barrier R.alloy (fun _ i => ((i:ℝ)+1)⁻¹) ∧ WilsonRootedPhysicalBright.Eligible R.kit ∧ (WilsonVacuumPreResetCurvatureReserve.Issued R.kit ∧ (WilsonRootedPhysicalCommonCut.Eligible R.kit ∧ other R.kit)) ∧
      WilsonMovingMentorSalary.Admitted ask R.kit := by
  exact WilsonMovingMentorCurvature.original.{u} ask hG hε J χ δ extra γ hγ
    (@Both G (@WilsonRootedPhysicalCommonCut.Eligible G) (@other))
    (fun s fee => FundedPredictionSupply.both
      (WilsonRootedPhysicalCommonCut.prepaid s fee) (funds s fee))

end YM.Integration.WilsonMovingMentorCommonCut
end
