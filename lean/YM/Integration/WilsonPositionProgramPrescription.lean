import YM.FVA2.Main
import YM.FVAAlt2.Rocket.Export

/-! The independent historical MS data, its entire prescribed bulk
counterterm, and the corrected field source of the original Wilson run.
The marked fees are selected once, before any profile, cutoff or period. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Land
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Rock Path Oceans
open Hem Mell Motif Literal Halo Alps Native Outlook High Detect Lifting Local.Physical
open Mach Train Pearl Emit Wind Wind.Leading Menus Program Knobs
open scoped Classical

theorem _root_.YM.Integration.WilsonPhysicalExteriorHistoricPrescription.on_team
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
namespace YM.Integration.WilsonPhysicalExteriorHistoricPrescription
open MS MS.Land FVA2 FVA2.Register PhysicalNext.Repeat.Legato
open RegulatorIR.FVAAlt2.Lodge YM.FVAAlt2

theorem booked {G:Gauge} (R:Run G) {hG:G.Simple} (N:WilsonPrescription G)
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S:Prescription (Press.portDeck G)} {dial:Bool} (matchMS:Main.Match N hG M S dial) :
    ∃ Q:Prescription (Press.portDeck G), Q.team=S.team ∧
      TaylorOKPl M (Lobby.Table (basisR R) (Press.portDeck G)) Q := by
  apply on_team M _ hG S
  rw [matchMS.matchingTeam]
  exact (Continuum.Continuation.plan (Reg.supplies N.scheme M) hG dial).taylor.bulk

end YM.Integration.WilsonPhysicalExteriorHistoricPrescription
end
