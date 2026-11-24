import YM.Integration.WilsonPhysicalStationMixedWickCapArchive
import YM.Integration.WilsonMeasuredSignedActionOwnedBook

/-! One cutoff lift on the exact submitted Vane at every small radius, for all future requested precisions. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickCapBook
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

open WilsonPhysicalStationMixedWickCapArchive (Seat)
open Set PhysMS.Frame WilsonMeasuredPublicEntranceNativeFrame
include simple in
theorem original (positive:0<δ)(made:C.Makes)(bliss:Bliss F l z H)
    (reached:∀s,(V s).wheel.r=s.val)(checked:∀s,(V s).checked f H (cap s))
    (calendar:∀s:ℕ→Set.Ioc (0:ℝ) δ,Tendsto (fun j=>(s j).val) atTop (𝓝 0) →
      Tendsto (fun j=>cap (s j)) atTop atTop ∧ Tendsto (fun j=>(V (s j)).k) atTop atTop)
    (dates:∀m:ℕ,∀ᶠr in trail,∀s:Set.Ioc (0:ℝ) δ,s.val=r→m≤(V s).k)
    (J:ℝ→tower S)(aligned:localCost trail (atRadius l cap V prior) J)
    (named:∀d,∀ᶠr in trail,obedient F H (J r) d):
    ∃A:ℝ→Group C D,WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=H) A J ∧
      ∀ᶠr in trail,∀s:Set.Ioc (0:ℝ) δ,s.val=r→Seat (f:=f) (l:=l) (H:=H) cap V prior D s (J r) (A r):=by
  classical
  let Ready (r:ℝ)(A:Group C D):Prop:=∃s:Set.Ioc (0:ℝ) δ,s.val=r ∧
    Seat (f:=f) (l:=l) (H:=H) cap V prior D s (J r) A
  have rows:=WilsonPhysicalStationMixedWickCapAxes.original F simple cap V made bliss reached checked calendar D
  have inside:∀ᶠr in trail,r<δ:=nhdsWithin_le_nhds (Iio_mem_nhds positive)
  have sale:∀ᶠr in trail,∃A:Group C D,Ready r A:=by
    filter_upwards [RG17.positiveLength,inside,rows,eventually_all.mpr (fun j:Fin (D+1)=>named j)] with r pos small stock valid
    let s:Set.Ioc (0:ℝ) δ:=⟨r,pos,small.le⟩
    obtain ⟨A,atHome⟩:=WilsonPhysicalStationMixedWickCapArchive.original F cap V prior D s (J r) (stock s rfl) (reached s) (checked s) valid
    exact ⟨A,s,rfl,atHome⟩
  obtain ⟨r₀,inhabited⟩:=sale.exists
  let A (r:ℝ):Group C D:=if ok:∃T:Group C D,Ready r T then ok.choose else inhabited.choose
  have issue:∀ᶠr in trail,Ready r (A r):=sale.mono fun r available=>by
    simpa only [A,dif_pos available] using available.choose_spec
  refine ⟨A,?_,?_⟩
  · intro m
    have nearby:=eventually_all.mpr fun i:Address C D=>Metric.tendsto_nhds.mp (aligned i.1 (entry i)) _ (cost_pos m)
    filter_upwards [issue,dates m,nearby] with r receipt date near
    obtain ⟨s,loc,fits,level,same,age,paid,place,actual,axes⟩:=receipt
    refine ⟨(date s loc).trans_eq age.symm,paid,place.trans loc,actual,fun j=>(axes j).2,fun i=>?_⟩
    change ‖(A r).change i.1 (entry i)-entry i‖≤costHint m
    rw [(axes i.1).1,loc]
    exact (dist_eq_norm ..).symm.trans_le (near i).le
  · filter_upwards [issue] with r event s same
    obtain ⟨t,located,real⟩:=event
    have eq:t=s:=Subtype.ext (located.trans same.symm)
    exact eq ▸ real

end YM.Integration.WilsonPhysicalStationMixedWickCapBook
end
