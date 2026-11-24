import YM.Integration.WilsonPhysicalWeakSundial
import YM.Integration.WilsonViewerElectedHierarchy
set_option autoImplicit false
universe u
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickPose
open PhysMS PhysMS.Frame
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot Next.UVStress Sundial
open MergeProof.East Next.Rank Next.Rank.East Maxwell
open scoped Topology ContDiff Classical BigOperators
section Physical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable {Y:Ultrafilter (ℕ×ℕ)} (h:G.Simple)(F:Final C f S)(H:(Bel C.book).Hierarchy)
  {Z:Terrace.Arch C} (hZ:Bliss F Y Z H)
local notation "K" => Maxwell.Free.scheme C.labels
set_option quotPrecheck false
local notation "D" d => (Bel C.book).Field d
def Finance :Prop:=∀φ P P',Target.XScheme F h H Y P P' φ →
  ∃a d e,Target.FieldComparison F H Z P P' a d e

def Receipt (P J:ℝ→tower S):Prop:=
  ∃(P':ℝ→change S 4)(φ:E4→ℝ)(a d e:ℝ→ℝ),(∀ᶠr in trail,J r 4=P' r) ∧
    Target.XScheme F h H Y (fun r=>P r 4) P' φ ∧ Target.FieldComparison F H Z (fun r=>P r 4) P' a d e

open private compose_pose from YM.Integration.WilsonPhysicalWeakSundial in
include hZ in
theorem original (paid:Finance (Y:=Y) (Z:=Z) h F H)(P:ℝ→tower S)
    (angle:PlotX F H Y h (fun r=>P r 4))(lead:Leading F P)(obeys:∀d,∀ᶠr in trail,obedient F H (P r) d):
    ∃J:ℝ→tower S,localCost trail P J ∧ Leading F J ∧ (∀d,∀ᶠr in trail,obedient F H (J r) d) ∧
      Receipt (Y:=Y) (Z:=Z) h F H P J:=by
  obtain ⟨φ,window⟩:=Work.A05.has_window Pith.sail Pith.sail_at
  obtain ⟨P',x,y,pose,norm⟩:=Sundial.spectrum_s F H h hZ angle (leading_chores F P lead) window
  have scheme:Target.XScheme F h H Y (fun r=>P r 4) P' φ:=⟨angle,leading_chores F P lead,⟨x,y,pose⟩,norm⟩
  obtain ⟨a,d,e,finance⟩:=paid φ _ P' scheme
  obtain ⟨J,same,near,turns,leadingJ⟩:=compose_pose h F H hZ P angle lead obeys pose norm
  exact ⟨J,near,leadingJ,turns,P',φ,a,d,e,same,scheme,finance⟩

end Physical
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Table
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{Y:Ultrafilter (ℕ×ℕ)}
    (h:G.Simple)(F:Final R.family f S)(H:(Bel R.family.book).Hierarchy){Z:Terrace.Arch R.family}
variable {L:EveryPhase.Almanac F}{Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J₀:ℝ→tower S}{cohort:Ultrafilter (ℕ×ℕ)→Prop}
theorem selected (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J₀ H Z Y h cohort)
    (paid:Finance (Y:=Y) (Z:=Z) h F H)(P:ℝ→tower S)(angle:PlotX F H Y h (fun r=>P r 4))
    (lead:Leading F P)(obeys:∀d,∀ᶠr in trail,obedient F H (P r) d):
    ∃J:ℝ→tower S,localCost trail P J ∧ Receipt (Y:=Y) (Z:=Z) h F H P J ∧
      WilsonViewerElectedHierarchy.Selected.{u} F L Q J H Z Y h cohort:=by
  obtain ⟨J,near,leadingJ,turns,posed⟩:=original h F H run.bliss paid P angle lead obeys
  obtain ⟨P',φ,a,d,e,same,scheme,comparison⟩:=posed
  exact ⟨J,near,⟨P',φ,a,d,e,same,scheme,comparison⟩,run.phases,run.trace,run.exclusion,run.facilities,
    run.foundation,run.sharp,run.bliss,run.original,run.retained,run.matrix,leadingJ,turns,
    ⟨fun r=>P r 4,P',φ,a,d,e,same,scheme,comparison⟩⟩

end YM.Integration.WilsonPhysicalStationMixedWickPose
end
