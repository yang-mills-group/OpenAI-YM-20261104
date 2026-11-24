import YM.Integration.WilsonMovingForkWeakWall
import YM.Integration.WilsonOriginalTwoFlatPublicBooks

/-! The same Buoys and weak sources and all their physical inverses are
chosen before a moving collection of radii, fields or locations is named. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonMovingForkWindowBooks
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

def Priced {r:ℝ}{D T:ℕ}(book:Book F (l:=l) H z D T r):Prop:=
  ∀d:Fin (D+1),∀v:S.Field d.val,‖(book.V d).symm v‖ ≤ dock r*cost F d.val r v

private def castArm {d:ℕ}{x y:S.Field d}(arm:Arm C S (l:Filter _) d x)(eq:x=y):
    Arm C S (l:Filter _) d y:=
  ⟨arm.source,arm.label,arm.approaches,arm.represents.trans eq⟩

private theorem mounted {r:ℝ}{D T:ℕ}
    (stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
      (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T))
    (weak:WilsonMovingForkWeakWall.Purchased F H l r D):
    Nonempty {B:Book F (l:=l) H z D T r // Priced F B}:=by
  classical
  obtain ⟨k,hk,W,good,atR,_live,_width,available⟩:=weak.station
  have each (d:Fin (D+1)):
      ∃T₀:Spin.change S d.val,(∀v:S.Field d.val,‖T₀.symm v‖≤dock r*cost F d.val r v) ∧
        Nonempty (Pair F stock (Nat.le_of_lt_succ d.isLt) W hk T₀ r):=by
    obtain ⟨T₀,bill,given⟩:=available d
    choose arm source cards using given
    let raw(y:S.Field d.val):Arm C S (l:Filter _) d.val y:=castArm (arm (T₀.symm y)) (T₀.apply_symm_apply y)
    let arms(b:Bool)(y:S.Field d.val):Arm C S (l:Filter _) d.val y:=
      if b then raw y else ((stock.department d.val (Nat.le_of_lt_succ d.isLt)).print y).arm
    exact ⟨T₀,bill,⟨⟨arms,fun _=>rfl,fun y q=>source (T₀.symm y) q,fun y=>cards (T₀.symm y)⟩⟩⟩
  choose V paid rows using each
  let B:Book F (l:=l) H z D T r:=⟨stock,k,W,hk,good,atR,V,fun e=>Classical.choice (rows e)⟩
  exact ⟨B,paid⟩

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(D:ℕ):
    ∃T:ℕ,∃δ:ℝ,0<δ ∧ ∃books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
      ∀s,Priced F (books s):=by
  classical
  obtain ⟨T,pooled⟩:=WilsonMeasuredPublicBank.before F l simple bliss D
  have buyers:=pooled Unit (fun _ r=>r) (fun _=>tendsto_id)
  have all:∀ᶠr in trail,Nonempty {B:Book F (l:=l) H z D T r // Priced F B}:=by
    filter_upwards [buyers,WilsonMovingForkWeakWall.original F simple bliss D] with r bank weak
    exact mounted F (bank.some ()) weak
  obtain ⟨δ,positive,inside⟩:=Metric.mem_nhdsWithin_iff.mp all
  have sold(s:{s:ℝ // 0<s ∧ s<δ}):Nonempty {B:Book F (l:=l) H z D T s.val // Priced F B}:=by
    apply inside
    refine ⟨?_,s.property.1⟩
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos s.property.1] using s.property.2
  exact ⟨T,δ,positive,fun s=>(sold s).some.val,fun s=>(sold s).some.property⟩

end YM.Integration.WilsonMovingForkWindowBooks
