import YM.Integration.WilsonPhysicalStationMixedWickCapAxes
import YM.Integration.WilsonPositionCapTransport
import YM.Integration.WilsonMovingForkReporterRestriction

/-! The full original cutoff lift and its calibrated change on the restriction of the elected Vane. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickCapArchive
open Function Filter Set Extraction Table Spec Lattice RG Wilson
open GapsContact GapsContact.Stamps GapsContact.Seams GapsContact.Ascent
open Trace Trace.Terrace Trace.Pilot Next.UVStress Climb MergeProof.East
open WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (simple : G.Simple) {l : Ultrafilter (ℕ×ℕ)}

open Trace.Over
open WilsonMovingForkReporterFilament
open WilsonMeasuredPublicEntranceNativeFrame (Priced)
variable {H:(Bel C.book).Hierarchy}{z:Arch C}

open Spin PhysMS PhysMS.Frame WilsonPositionThermometerOrientedStation

open WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonMeasuredPublicEntranceNativeFrame (atRadius)
open WilsonPhysicalStationMixedWickCapAxes (Signed)
variable {δ:ℝ}(cap:Set.Ioc (0:ℝ) δ→ℕ)(V:∀s,Vane C (cap s))(prior:ℝ→tower S)(D:ℕ)

def Seat (s:Set.Ioc (0:ℝ) δ)(Q:tower S)(A:Group C D):Prop:=
  ∃fits:D≤cap s,A.horizon=D ∧ HEq A.station (WilsonMovingForkReporterRestriction.vane fits (V s)) ∧
    A.station.k=(V s).k ∧ A.station.checked f H A.horizon ∧ A.station.wheel.r=s.val ∧
    Tendsto A.station.wheel.atCut (l:Filter _) (𝓝 A.lift) ∧
    ∀j:Fin (D+1),A.change j=(Q j).trans (atRadius l cap V prior s.val j).symm ∧
      Coherent H.spin H.spin j (A.change j) ∧ A.change j ((Bel C.book).unit j)=(Bel C.book).unit j ∧
      ∀x,Q j x=S.project j (A.lift (index A j) (A.change j x))

theorem original (s:Set.Ioc (0:ℝ) δ)(Q:tower S)(rows:WilsonPhysicalStationMixedWickCapAxes.Signed F (H:=H) (l:=l) (V s) D)
    (atHome:(V s).wheel.r=s.val)(stock:(V s).checked f H (cap s))
    (right:∀j:Fin (D+1),obedient F H Q j):
    ∃A:Group C D,Seat (f:=f) (l:=l) (H:=H) cap V prior D s Q A:=by
  classical
  choose U filed orientation using rows.filed
  choose Y live represents using fun j=>filed j
  let W:=WilsonMovingForkReporterRestriction.vane rows.fits (V s)
  let A:Group C D:=⟨D,le_rfl,W,Y,fun j=>(Q j).trans (U j).symm⟩
  have drawn:Tendsto W.wheel.atCut (l:Filter _) (𝓝 Y):=
    tendsto_pi_nhds.mpr fun j=>live j
  refine ⟨A,rows.fits,rfl,HEq.rfl,rfl,WilsonMovingForkReporterRestriction.checked rows.fits (V s) stock,
    atHome,drawn,fun j=>?_⟩
  have fits:j.val≤cap s:=(Nat.le_of_lt_succ j.isLt).trans rows.fits
  have same:=WilsonMeasuredPublicEntranceNativeFrame.at_site l cap V prior s fits (filed j)
  refine ⟨?_,(orientation j Q (right j)).1,(orientation j Q (right j)).2,fun x=>?_⟩
  · change (Q j).trans (U j).symm=(Q j).trans (atRadius l cap V prior s.val j).symm
    rw [same]
  · change Q j x=S.project j (Y j ((U j).symm (Q j x)))
    rw [←represents j,LinearEquiv.apply_symm_apply]

end YM.Integration.WilsonPhysicalStationMixedWickCapArchive
end
