import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressMenus
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressEntry
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Table
open PhysMS.Frame WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open scoped Topology BigOperators Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true


open scoped Matrix


open WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows


variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}

open WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressMenus
theorem filed (F:Final C f S)(X:Scaling S)(k:ℕ){n:ℕ}
    (q:Fin n→(Bel C.book).Tag)(marks:Fin n→Bool)(ab:Fin n→Axis×Axis):
    Pert.scaledPhysical X F.sector.energy k q marks ab =
      fun i=>⟨height (q i) (marks i),X.U k (height (q i) (marks i)) (pupil F X (q i) (ab i) k (marks i))⟩:=by
  funext i
  cases key:marks i
  · simp [Pert.scaledPhysical,key,height,pupil]
    rfl
  · simp [Pert.scaledPhysical,key,height,pupil]
    unfold WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows.born
    calc
      _=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows.physical F X k (ab i).1 (ab i).2:=by simp [WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows.physical]
      _=_:=((X.U k 4).apply_symm_apply (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows.physical F X k (ab i).1 (ab i).2)).symm

theorem original (F:Final C f S)(X:Scaling S)(k:ℕ){n:ℕ}
    (q:Fin n→(Bel C.book).Tag)(marks:Fin n→Bool)(ab:Fin n→Axis×Axis)(p:Viewers F):
    measured F p (X.U k) (fun i=>pupil F X (q i) (ab i) k (marks i)) (X.r k)=
      fun x=>S.useAt (spectator F p) (X.r k • x) (Pert.scaledPhysical X F.sector.energy k q marks ab):=by
  rw [filed F X]
  rfl

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressEntry
end
