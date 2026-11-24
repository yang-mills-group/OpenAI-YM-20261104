import YM.Integration.WilsonAddressedPublicCardBooks
import YM.Integration.WilsonPhysicalWeakWallSequence

/-! The actual moving detector Book retains the same signed weak home used by the public slice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakWallBooks
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

def Shared {D T:ℕ}{r:ℝ}(B:Book F (l:=l) H z D T r)(w:Seats C S D):Prop:=
  Housed F B ∧ B.k=w.room.horizon ∧ HEq B.W w.room.station ∧ B.V=w.turn

private theorem mounted {r:ℝ}{D T:ℕ}
    (stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
      (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T))
    (w:Seats C S D)(good:w.room.station.checked order H w.room.horizon)(atR:w.room.station.wheel.r=r)
    (fare:WilsonPhysicalWeakWheelOffers.Offered F (l:=l) w.room.fits w.room.station r w.turn):
    Nonempty {B:Book F (l:=l) H z D T r // Shared F B w}:=by
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

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(D:ℕ){I:Type}[Fintype I]
    (d:I→Fin (D+1))(v:∀i,(Bel R.family.book).Field (d i)):
    ∃w:ℝ→Seats C S D,(∀m:ℕ,∀ᶠr in trail,Booked (Y:=l) simple F H d v (w r) r m) ∧
      ∃T:ℕ,∃δ:ℝ,0<δ ∧ ∃books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
        ∀s,Shared F (books s) (w s.val):=by
  classical
  obtain ⟨w,ready⟩:=WilsonPhysicalWeakWallSequence.original simple F H bliss d v
  obtain ⟨T,pooled⟩:=WilsonMeasuredPublicBank.before F l simple bliss D
  have buyers:=pooled Unit (fun _ r=>r) (fun _=>tendsto_id)
  have all:∀ᶠr in trail,Nonempty {B:Book F (l:=l) H z D T r // Shared F B (w r)}:=by
    filter_upwards [buyers,ready 0] with r pool desk
    have station:=(desk.2.2 0 le_rfl).2
    exact mounted F (pool.some ()) _ station.2.1 station.2.2.1 desk.1
  obtain ⟨δ,positive,inside⟩:=Metric.mem_nhdsWithin_iff.mp all
  have sold(s:{s:ℝ // 0<s ∧ s<δ}):Nonempty {B:Book F (l:=l) H z D T s.val // Shared F B (w s.val)}:=by
    apply inside
    refine ⟨?_,s.property.1⟩
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos s.property.1] using s.property.2
  exact ⟨w,ready,T,δ,positive,fun s=>(sold s).some.val,fun s=>(sold s).some.property⟩

end YM.Integration.WilsonPhysicalWeakWallBooks
