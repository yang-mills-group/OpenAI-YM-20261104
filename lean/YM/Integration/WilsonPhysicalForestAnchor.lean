import YM.Integration.WilsonPhysicalAnchoredPaths
import YM.MSbar.Heath.Charts

/-! Use the genuine nonlinear conditional's own block forest as the first
part of the gauge transport. Only its remaining block-root colours are
rotated; the support bill is on the actual fine periodic lattice. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalForestAnchor
open Lattice RG Wilson Tree
open WilsonPhysicalAnchoredGauge WilsonPhysicalAnchoredPaths
open scoped Classical BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f}

def foot (S:StepData c f) (x:Site f) := S.ratio.embed (S.ratio.parent x)

def roads (F:Forest S.ratio) (o:Site f): Roads f where
  root:=o
  arm x:=F.hike x ++ (WilsonPhysicalAnchoredPaths.roads o).arm (foot S x)
  closed x:=by rw [stop_append,F.hike_root];exact (WilsonPhysicalAnchoredPaths.roads o).closed _

theorem after_forest (F:Forest S.ratio) (o:Site f) (U:Config G f) :
    based (roads F o) U=Lattice.gauge (fun x=>transport (WilsonPhysicalAnchoredPaths.roads o) U (foot S x))
      (MSbar.Heath.canoe F U) := by
  have one (x:Site f) : transport (roads F o) U x=
      transport (WilsonPhysicalAnchoredPaths.roads o) U (foot S x) * F.foldAt U x := by
    unfold transport roads Tree.Forest.foldAt
    rw [travel_append,F.hike_root,mul_inv_rev];rfl
  funext e
  unfold based MSbar.Heath.canoe Lattice.gauge
  rw [one,one];group

/-- The fine tree leg costs at most 4L; after that leg the remaining route
to the anchor has length ≤4(D+4L). -/
theorem charged_length (F:Forest S.ratio) (o x:Site f) :
    ((roads F o).arm x).length≤4*separation o x+20*S.ratio.count.val := by
  have first:=(F.hike_lower x).trans (F.bound x)
  have h:=Push.Uniform.stop_length x (F.hike x)
  rw [F.hike_root] at h
  have dist:=separation_triangle o x (foot S x)
  have last:=WilsonPhysicalAnchoredPaths.length o (foot S x)
  change separation x (foot S x)≤(F.hike x).length at h
  change (F.hike x ++ (WilsonPhysicalAnchoredPaths.roads o).arm (foot S x)).length≤_
  rw [List.length_append];omega

theorem localized {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F:Forest S.ratio) (o:Site f)
    (X:Support f) (D:ℕ) (rad:∀x∈X,separation o x≤D) {B:Config G f→E} (h:LocalOn (X:Set (Site f)) B) :
    GaugeInvariant (representative (roads F o) B) ∧
    LocalOn (halo (4*D+20*S.ratio.count.val) X:Set (Site f)) (representative (roads F o) B) := by
  have col:collar (roads F o) (X:Set (Site f))⊆(halo (4*D+20*S.ratio.count.val) X:Set (Site f)):=by
    intro y hy
    rcases hy with h|⟨x,hx,hxy⟩
    · exact halo_subset _ _ h
    exact halo_spec.mpr ⟨x,hx,(visited x y _ hxy).trans ((charged_length F o x).trans (by have bound:=rad x hx;omega))⟩
  refine ⟨invariant (roads F o) B,fun U V agree=>support _ h U V ?_⟩
  intro e he hb;exact agree e (col he) (col hb)

end YM.Integration.WilsonPhysicalForestAnchor
