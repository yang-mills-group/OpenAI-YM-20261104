import YM.FVA2.Main
import YM.FVAAlt2.Plus.High
import YM.Integration.WilsonMatrixTicketLanesMatchedProfiles

/-! The genuine main MS prescription buys the corrected marked field book on the very same original Wilson run. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Land
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Rock Path Oceans
open Hem Mell Motif Literal Halo Alps Native Outlook High Detect Lifting Local.Physical
open Mach Train Pearl Emit Wind Wind.Leading Menus Program Knobs
open scoped Classical

theorem _root_.YM.Integration.WilsonMatrixTicketLanesFundedScheme.marked
    {G:Gauge} {B:Deck G} {A:Booked B} (M:MS_Data G A)
    (V:RichBook B) (hG:G.Simple) (P:Prescription B)
    (bulk:Fixed (col (skyline G P.team)) (Archive 4 M.bulk) true 4 1) :
    ∃ Q:Prescription B, Q.team=P.team ∧ TaylorOKPl M V Q := by
  have one (d:ℕ) (i:Plaid B d) := physicalAtPl V (j:=read i) hG bulk
    (Outlook.fieldD M.bulkOK (M.markOK d i) wisdom ((A.law d i).moodQ))
    (initialHF (A.law d i) (sizeG i) (M.markOK d i))
  choose fees fit marks using one
  exact ⟨⟨P.team,fees,fit⟩,rfl,bulk,marks⟩

end YM.MS.Land

namespace YM.Integration.WilsonMatrixTicketLanesFundedScheme
open MS MS.Land FVA2 FVA2.Register PhysicalNext.Repeat.Legato
open RegulatorIR.FVAAlt2.Lodge YM.FVAAlt2
open scoped Classical
variable {G : Gauge}

/-- The submitted Main.Match prescribes the team; the same actual registered fields then match at every profile. -/
theorem existing (R : Run G) (N : WilsonPrescription G) {simple : G.Simple}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {S : Prescription (Press.portDeck G)} {dial : Bool}
    (matched : Main.Match N simple M S dial) :
    ∃ Q : Prescription (Press.portDeck G), Q.team=S.team ∧ TaylorOKPl M (Lobby.Table (basisR R) (Press.portDeck G)) Q ∧
      MixedStory.AllProfiles M (WilsonMatrixTicketLanesNativePrices.warehouse R) Q := by
  have bulk := (Continuum.Continuation.plan (Reg.supplies N.scheme M) simple dial).taylor.bulk
  rw [← matched.matchingTeam] at bulk
  obtain ⟨Q,team,taylor⟩ := marked M (Lobby.Table (basisR R) (Press.portDeck G)) simple S bulk
  exact ⟨Q,team,taylor,WilsonMatrixTicketLanesMatchedProfiles.original R M Q taylor simple⟩

/-- The independent bulk prescription and its marked book are paid before the observed positions or velocities. -/
theorem original (R : Run G) (simple : G.Simple) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (dial : Bool) :
    ∃ S Q : Prescription (Press.portDeck G), Main.Match N simple M S dial ∧ Q.team=S.team ∧
      TaylorOKPl M (Lobby.Table (basisR R) (Press.portDeck G)) Q ∧
      MixedStory.AllProfiles M (WilsonMatrixTicketLanesNativePrices.warehouse R) Q := by
  obtain ⟨S,matched⟩ := Main.wilson_to_MS N simple M dial
  obtain ⟨Q,team,taylor,all⟩ := existing R N matched
  exact ⟨S,Q,matched,team,taylor,all⟩

end YM.Integration.WilsonMatrixTicketLanesFundedScheme
