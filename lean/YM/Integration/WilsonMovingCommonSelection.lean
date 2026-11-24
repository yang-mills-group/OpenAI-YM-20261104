import YM.Integration.WilsonGaussianDeterminantTender
import YM.Integration.WilsonMovingLogForecast
import YM.Integration.WilsonMovingChartReserve
import YM.Integration.WilsonMovingSensorReserve

/-! The actual decorated and determinant conductor, original chart expense,
short-log provider and finite winding sensors use a single funded run. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingCommonSelection
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

theorem purchased {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi) (δ : Charity.RG12.Decal G)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ)
    (other:FundedCompanySelection.Prediction G) (funds:FundedPredictionSupply.AllPrices (@other)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
      (affine : ManuscriptQLocalCofinalAffineFields.Paid R)
      (paid : QLocalRequestedSectorCalendar.Paid J (joined G J χ δ) extra γ R.kit),
      WilsonRootedPhysicalSpringGaussian.Receipt.{u} hG ε J extra γ ManuscriptQLocalCofinalAffineFields.schedule
        R T W affine.1 ∧
      ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧
      (∀ through, ∃ first, WilsonRootedPhysicalSpringAffineRows.After R affine through first) ∧
      WilsonGaussianDeterminantTender.On R J χ δ extra γ paid ∧
      RG01Estimate.Chart.Barrier R.alloy (fun _ _=>1) ∧
      Juniper.Mulberry.Lanterns R.kit.shape R.alloy.delay ∧ WilsonMovingSensorReserve.Extra R.kit ∧ other R.kit := by
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
  obtain ⟨R,T,W,affine,receipts,physical,jets,rows⟩:=
    WilsonRootedPhysicalSpringAffineRows.purchasedWith.{u} hG hε J extra γ hγ (@all) pay
  exact ⟨R,T,W,affine,receipts.1,physical,jets,rows,WilsonGaussianDeterminantTender.opens R J χ δ extra γ receipts.1 hG,
    receipts.2.1,receipts.2.2.1,receipts.2.2.2.1,receipts.2.2.2.2⟩

end YM.Integration.WilsonMovingCommonSelection
end
