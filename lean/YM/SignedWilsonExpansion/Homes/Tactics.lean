import YM.Extraction.Inherited
import YM.TraceExtension.Prom.Zoom.Boats

/-! Select the FULL mesh refinement without changing the period -/
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Homes
open Function Set Filter Extraction
open scoped Topology BigOperators

def track (f:Order):Order := Order.mk .full f.per

variable (f:Order)
theorem track_per : (track f).per=f.per := rfl
@[simp] theorem track_mesh : (track f).mesh=.full := rfl
@[simp] theorem track_smaller : (track f).refine ⟨f.mesh,.full⟩ = f:=by cases f; rfl

theorem availablePV : f.fuse ≤ (track f).fuse := by
   apply le_def.mpr; intro s hs
   change f.late (fun N p => (N,p) ∈ s)
   convert ((track f).late_refine ⟨f.mesh,.full⟩ (show (track f).late (fun N p => (N,p) ∈ s) from hs)) using 1
   rw [track_smaller]

open MergeProof.East Next.Rank
variable {G:Gauge} {C:Family G} (F:Extraction.Order) (H:(Cells.standard C).Hierarchy)
theorem refreshedPV {n i : ℕ} (V : Vane C n) (v: V.checked (track F) H i) : V.checked F H i := by
   refine ⟨v.high,v.early,v.rate,v.plate,?_⟩
   have h:=Next.UVStress.Station.refreshed _ v.fares ⟨F.mesh,.full⟩
   rwa [track_smaller] at h
end YM.SignedWilsonExpansion.Homes
