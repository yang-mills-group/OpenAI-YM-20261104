import YM.Integration.WilsonGaussianDeterminantTender
import YM.Integration.WilsonCoherentMayerCovarianceCalendar
import YM.Integration.WilsonRootedPhysicalSpringReportedMS

/-! One original existence run funds the prescribed MS calculation and the physical word,
the full normalized Gaussian determinant and the conditional covariance bound. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantReportedMS
open Lattice RG RG.Supply PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FVA2 FVA2.CityHistory FVA2.Register FVAAlt2 FormalOPE.RG10.BlockGauge
open MS MS.Rake MS.Land MS.Tide MS.Orbit MS.Dial MS.Fleet MS.Local.Physical
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open FullQLocal FullQLocal.RenderedStep Org Progress.DirectedRecipe
open ConnectedActivityE6 Push.SectorMeasure
universe u

theorem purchased {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) (calendar : XSpace.Run) (dial : Bool) :
    ∃ (N : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S : Prescription (Press.portDeck G)), N.run=calendar ∧ Main.Match N simple M S dial ∧
      ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (affine : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G))
        (booking : QLocalRequestedSectorCalendar.Paid J
          (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
          extra γ R.kit),
        WilsonRootedPhysicalSpringReportedMS.Settled.{u} simple ε J extra γ M S R T W affine Q ∧
          WilsonGaussianDeterminantTender.On R J χ (WilsonCoherentMayerCovarianceCalendar.decal G)
            extra γ booking := by
  let δ := WilsonCoherentMayerCovarianceCalendar.decal G
  let joint := WilsonGaussianDeterminantTender.joined G J χ δ
  obtain ⟨N,M,S,clock,matched,R,T,W,affine,Q,booking,report⟩ :=
    WilsonRootedPhysicalSpringReportedMS.purchasedWith.{u} simple hε J extra γ hγ calendar dial
      (@QLocalRequestedSectorCalendar.Paid G V J joint extra γ)
      (fun s t => QLocalRequestedSectorCalendar.prepaid J joint extra γ simple hγ s (ThroughLaunch.raging s t))
  exact ⟨N,M,S,clock,matched,R,T,W,affine,Q,booking,report,
    WilsonGaussianDeterminantTender.opens R J χ δ extra γ booking simple⟩

end YM.Integration.WilsonGaussianDeterminantReportedMS
