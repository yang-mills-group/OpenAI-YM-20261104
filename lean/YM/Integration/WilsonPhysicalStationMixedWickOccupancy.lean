import YM.Integration.WilsonPhysicalStationMixedWickSolvent
import YM.Integration.WilsonMovingForkReporterMixedFitting
import YM.Integration.WilsonMovingForkReporterMixedHouses

/-! Complete lower electrodes and additional fields on one original attendance. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickOccupancy
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open Next.Rank.Ribbon Table Trace.Pilot Trace PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical


open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonMovingForkReporterMixedHouses (Held)
open WilsonPhysicalStationMixedBasisSale (Sold)
open WilsonPhysicalStationMixedWickNamedGram (electrode)
open scoped Classical


open scoped Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    (B:Binding R.family)(O:HaarBudget G)(χ:ChartRatio G)(price:ℕ→ℝ)
    (qty:ℕ→ℕ)(menu:∀D,Fin (qty D)→Slot R.family)
    {I:Type*}{l:Filter I}{D h:I→ℕ}(P:∀i,Tapes.Panel (D i))(V:∀i,Vane R.family (h i))
local notation "AX"=>R.family.path.levels

theorem original (afford:∀ᶠi in l,Held (f:=f) R B O χ H price qty menu (P i) (V i))
    (late:Tendsto (fun i=>(V i).k) l atTop)(simple:G.Simple)(x:Points 2)(gen:x∈generic 2)
    (A:Set (Points 2))(near:A∈𝓝 x):
    Tendsto (fun i=>tested AX (V i).b (V i).k x) l (𝓝 x) ∧
      ∀ᶠi in l,tested AX (V i).b (V i).k x∈A ∧ FitSky AX (V i).b (V i).k x:=by
  have issued:=WilsonMovingForkReporterMixedFitting.original P V (afford.mono (fun i fund=>fund.choose_spec.1))
    late simple x gen
  exact ⟨issued.1,(issued.1.eventually near).and issued.2⟩

end YM.Integration.WilsonPhysicalStationMixedWickOccupancy
end
