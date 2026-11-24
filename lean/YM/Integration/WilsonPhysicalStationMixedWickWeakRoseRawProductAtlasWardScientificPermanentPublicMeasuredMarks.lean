import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseLeading
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMeasuredMarks
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Table
open PhysMS.Frame WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open scoped Topology BigOperators Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true



variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
theorem orderZero {n:ℕ}(x:Points n)(F G:Points n→ℂ):
    ‖iteratedFDeriv ℝ 0 F x-iteratedFDeriv ℝ 0 G x‖=‖F x-G x‖:=by
  calc
    _=‖iteratedFDeriv ℝ 0 (fun y=>F y-G y) x‖:=by
      congr 1
    _=‖F x-G x‖:=norm_iteratedFDeriv_zero

theorem original (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X){n:ℕ}
    (q:Fin n→(Bel C.book).Tag)(mask:Fin n→Bool)(ab:Fin n→Axis×Axis)(x:Points n)(separated:x∈conf n):
    Tendsto (fun k:ℕ=>Ward.disc (Pert.scaledPhysical X F.sector.energy k q mask ab) (X.r k • x)) atTop
      (𝓝 (Ward.disc (Pert.freeWithStress C.labels q mask ab) x)):=by
  apply Metric.tendsto_nhds.mpr
  intro ε pos
  have bill:=first.jets n 0 q mask ab isCompact_singleton (Set.singleton_subset_iff.mpr separated) (half_pos pos)
  filter_upwards [bill] with k right
  have cost:=right x (Set.mem_singleton x)
  rw [orderZero] at cost
  rw [dist_eq_norm]
  exact lt_of_le_of_lt cost (half_lt_self pos)

theorem unmarked (F:Final C f S)(X:Scaling S)(first:Pert.FirstExtension F X){n:ℕ}
    (d:Caps n)(v:MaxwellSlots C d)(x:Points n)(sep:x∈conf n):
    Tendsto (fun k:ℕ=>measured F none (X.U k) v (X.r k) x) atTop (𝓝 (WickGoal v x)):=by
  exact original F X first (fun i=>⟨d i,v i⟩) (fun _=>false) (fun _=>(0,0)) x sep

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMeasuredMarks
end
