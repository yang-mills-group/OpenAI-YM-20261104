import YM.Integration.WilsonPhysicalWeakRisingStaff

/-! Restrict a purchased rising physical family without replacing its Vane, turn or raw cutoff field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakSameStation
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}
local notation "C" => R.family
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourSquare

open WilsonAddressedPublicCardBooks (Housed)
open WilsonPhysicalWeakWallStaff (Seats Booked)
open private castArm from YM.Integration.WilsonAddressedPublicCardBooks

open WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakWallBounded
def widen {d e:ℕ}(h:d≤e)(i:Fin (d+1)):Fin (e+1):=⟨i.val,i.isLt.trans_le (Nat.succ_le_succ h)⟩

def trim {d e:ℕ}(h:d≤e)(w:Seats C S e):Seats C S d:=
  ⟨w.frame,⟨w.room.horizon,h.trans w.room.fits,w.room.station,w.room.lift,
    fun j=>w.room.change (widen h j)⟩,fun j=>w.turn (widen h j)⟩

theorem admitted {e d m:ℕ}(h:d≤e)(hm:m≤e)(simple:G.Simple){r:ℝ}(w:Seats C S e)
    (sale:Booked (Y:=l) simple F H (fun i:slot C e=>i.1) (head C) w r e):
    Booked (Y:=l) simple F H (fun i:slot C d=>i.1) (head C) (trim h w) r m:=by
  refine ⟨⟨h.trans sale.1.live,sale.1.width,sale.1.physical,sale.1.blocks,fun j=>sale.1.rows (widen h j)⟩,
    fun j=>sale.2.1 (widen h j),?_⟩
  intro a ha
  obtain ⟨staff,age,thick,home,returns,agrees,near⟩:=sale.2.2 a (ha.trans hm)
  exact ⟨staff,age,thick,home,returns,fun j=>agrees (widen h j),
    fun j=>near ⟨widen h j.1,j.2⟩⟩

private theorem mount {r:ℝ}{D T:ℕ}
    (stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
      (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T))
    (w:Seats C S D)(good:w.room.station.checked order H w.room.horizon)(atR:w.room.station.wheel.r=r)
    (fare:WilsonPhysicalWeakWheelOffers.Offered F (l:=l) w.room.fits w.room.station r w.turn):
    Nonempty {B:Book F (l:=l) H z D T r // WilsonPhysicalWeakWallBooks.Shared F B w}:=by
  classical
  have passengers(e:Fin (D+1)):Nonempty (Pair F stock (Nat.le_of_lt_succ e.isLt)
      w.room.station w.room.fits (w.turn e) r):=by
    choose arm source cards using (fare.rows e).2
    let T₀:=w.turn e
    let act(v:S.Field e):Arm C S (l:Filter _) e v:=castArm (arm (T₀.symm v)) (T₀.apply_symm_apply v)
    let arms(b:Bool)(v:S.Field e):Arm C S (l:Filter _) e v:=
      if b then act v else ((stock.department e (Nat.le_of_lt_succ e.isLt)).print v).arm
    exact ⟨⟨arms,fun _=>rfl,fun v t=>source (T₀.symm v) t,fun v=>cards (T₀.symm v)⟩⟩
  let B:Book F (l:=l) H z D T r:=
    ⟨stock,w.room.horizon,w.room.station,w.room.fits,good,atR,w.turn,fun e=>(passengers e).some⟩
  exact ⟨B,⟨fun e=>(fare.rows e).1,fare.width.1,fare.width.2.1,fare.width.2.2,fare.physical,fare.blocks⟩,
    rfl,HEq.rfl,rfl⟩

theorem books (simple:G.Simple)(bliss:Bliss F l z H)(day:ℝ→Day C S)
    (rises:Tendsto (fun r=>(day r).1) trail atTop)
    (sold:∀ᶠr in trail,Served (Y:=l) simple F H (day r) r)(D:ℕ):
    ∃T:ℕ,∃δ:ℝ,0<δ ∧ ∃books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
      ∀s,∃le:D≤(day s.val).1,WilsonPhysicalWeakWallBooks.Shared F (books s) (trim le (day s.val).2):=by
  classical
  obtain ⟨T,pooled⟩:=WilsonMeasuredPublicBank.before F l simple bliss D
  have buyers:=pooled Unit (fun _ r=>r) (fun _=>tendsto_id)
  have all:∀ᶠr in trail,Nonempty {B:Book F (l:=l) H z D T r // ∃le:D≤(day r).1,
      WilsonPhysicalWeakWallBooks.Shared F B (trim le (day r).2)}:=by
    filter_upwards [buyers,sold,rises.eventually_ge_atTop D] with r pool sale cap
    have bounded:=admitted F cap (Nat.zero_le _) simple (day r).2 sale
    have station:=(bounded.2.2 0 le_rfl).2
    obtain ⟨B,shared⟩:=mount F (pool.some ()) _ station.2.1 station.2.2.1 bounded.1
    exact ⟨B,cap,shared⟩
  obtain ⟨δ,dp,inside⟩:=Metric.mem_nhdsWithin_iff.mp all
  have active(s:{s:ℝ//0<s ∧ s<δ}):Nonempty {B:Book F (l:=l) H z D T s.val //
      ∃le:D≤(day s.val).1,WilsonPhysicalWeakWallBooks.Shared F B (trim le (day s.val).2)}:=by
    apply inside
    refine ⟨?_,s.property.1⟩
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos s.property.1] using s.property.2
  exact ⟨T,δ,dp,fun s=>(active s).some.val,fun s=>(active s).some.property⟩

end YM.Integration.WilsonPhysicalWeakSameStation
