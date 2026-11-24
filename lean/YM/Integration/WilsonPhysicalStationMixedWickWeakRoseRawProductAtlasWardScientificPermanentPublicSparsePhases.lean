import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseLeading
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparsePhases
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Table
open PhysMS.Frame WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open scoped Topology BigOperators Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true



variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
theorem original (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X)
    (J:ℝ→PhysMS.tower S)(leading:Leading F J)(simple:G.Simple)
    (Q:OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(foundation:OPE.Orbits.Foundation F Q)
    {n:ℕ}(d:Caps n)(v:MaxwellSlots C d)(j:ℕ){K:Set (Points n)}(compact:IsCompact K)(inside:K⊆conf n):
    (∀k:ℕ,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame.splice X J (X.r k)=X.U k) ∧
    ∀ᶠ k:ℕ in atTop,∀x∈K,∀p q:Viewers F,
      ‖iteratedFDeriv ℝ j (measured F p (X.U k) v (X.r k)) x-
        iteratedFDeriv ℝ j (measured F q (X.U k) v (X.r k)) x‖≤(X.r k)^3:=by
  obtain ⟨fixed,price⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseLeading.original F X first J leading
  obtain ⟨M,hM,η,hη,room⟩:=compact_within K compact inside
  have fee:=PhysMS.Frame.within_price F Q (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame.splice X J) price simple X foundation M η 1 j v zero_lt_one hM hη
  refine ⟨fixed,?_⟩
  filter_upwards [(WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame.sparse X).eventually fee] with k enclosed x hx p q
  have earned:=enclosed x (room x hx) p q
  rw [fixed k] at earned
  simpa only [show (4:ℝ)-1=(3:ℕ) by norm_num,Real.rpow_natCast] using earned

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparsePhases
end
