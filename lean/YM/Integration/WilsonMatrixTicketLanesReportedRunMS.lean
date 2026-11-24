import YM.Integration.WilsonMatrixTicketLanesReportedRun
import YM.Integration.WilsonMatrixTicketLanesFundedScheme

/-! One matched marked prescription on the original Wilson run, paid for all actual reporting dates and extraction orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedRunMS
open MS MS.Land FVA2 FVA2.Register PhysicalNext.Repeat.Legato
open RegulatorIR.FVAAlt2.Lodge YM.FVAAlt2
open scoped Classical
variable {G : Gauge}

/-- Keep the independent marked prescription fixed before all matrix labels, relative positions,
finite coefficient grades, tolerances and requested powers on the original running Wilson coupling. -/
theorem original (R : Run G) (simple : G.Simple) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (dial : Bool) :
    ∃ S Q : Prescription (Press.portDeck G), Main.Match N simple M S dial ∧ Q.team=S.team ∧
      TaylorOKPl M (Lobby.Table (basisR R) (Press.portDeck G)) Q ∧
      MixedStory.AllProfiles M (WilsonMatrixTicketLanesNativePrices.warehouse R) Q ∧
      ∀ (f : Extraction.Order) (J : ℕ) (hJ : 0 < J) (c : ℝ) (hc : 1 < c),
        WilsonMatrixTicketLanesReportedRun.Statement R M Q f simple J hJ hc := by
  obtain ⟨S,Q,matchMS,team,taylor,tested⟩ := WilsonMatrixTicketLanesFundedScheme.original R simple N M dial
  exact ⟨S,Q,matchMS,team,taylor,tested,fun f J hJ _ hc => WilsonMatrixTicketLanesReportedRun.original R M Q taylor f simple J hJ hc⟩

end YM.Integration.WilsonMatrixTicketLanesReportedRunMS
