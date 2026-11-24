import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressDetector
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
variable {G:Gauge}{C:Family G}
def survey (C:Family G)(w:Maxwell.ProbeFamily G):Survey C:=
  ⟨w.n,fun i=>⟨w.d i,(Maxwell.Free.fields C.labels _).symm (w.exterior i)⟩,w.x,w.clear⟩

theorem placed (w:Maxwell.ProbeFamily G)(u:(Bel C.book).Field 4):
    free (survey C w) u=w.test 4 (Maxwell.Free.fields C.labels 4 u):=by
  rw [Maxwell.test_formula]
  change ((Bel C.book).useAt (Bel C.book) w.x (tickets (survey C w) u))=_
  rw [Maxwell.Free.display]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [Function.comp_apply,Maxwell.Free.supply,Maxwell.Free.address,tickets,seats,dims,survey]
    rfl
  · simp [Function.comp_apply,Maxwell.Free.supply,Maxwell.Free.address,tickets,seats,fixed,dims,survey]
    change (Maxwell.Free.fields C.labels (w.d j) ((Maxwell.Free.fields C.labels (w.d j)).symm (w.exterior j))).val=(w.exterior j).val
    rw [LinearEquiv.apply_symm_apply]

theorem separates (u:(Bel C.book).Field 4)(all:∀P:Survey C,free P u=0):u=0:=by
  have empty:Maxwell.Free.fields C.labels 4 u∈Maxwell.residual G 4:=by
    rw [Maxwell.residual,LinearMap.mem_ker]
    funext w
    exact (placed (C:=C) w u).symm.trans (all (survey C w))
  rw [Maxwell.Free.no_residual,Submodule.mem_bot] at empty
  exact (Maxwell.Free.fields C.labels 4).injective (empty.trans (map_zero _).symm)

theorem original : Submodule.span ℂ (Set.range (free (C:=C)))=⊤:=by
  let D:=Submodule.span ℂ (Set.range (free (C:=C)))
  have zero:D.dualCoannihilator=⊥:=by
    apply le_antisymm _ bot_le
    intro x h
    change x=0
    apply separates
    intro P
    exact (Submodule.mem_dualCoannihilator x).mp h _ (Submodule.subset_span ⟨P,rfl⟩)
  change D=⊤
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W:=D),zero,Submodule.dualAnnihilator_bot]

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressDetector
end
