import YM.Integration.WilsonReflectedMixedMasterSchool
import YM.Integration.WilsonReflectedMixedPresoldTrial
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReflectedMixedSharedAxis
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
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS


open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory WilsonMeasuredPublicEntranceHeadBoard
open WilsonAddressedAlignedColumn WilsonReflectedPublicStationFare
open WilsonThermometerOffsetCylinder WilsonThermometerOffsetTrajectory


open WilsonReflectedMixedMasterAxes (Fixed)
open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)

open WilsonReflectedMixedMasterRegistry (Gallery Delivery)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
def Pinned (D T h t:ℕ)(d:I→Fin (D+1))(e:I→ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (M:I→ℝ)(ceiling:ℝ)(power target:ℕ)(ρ:I→{s:ℝ // 0<s ∧ s<δ})(f K:ℕ):Prop:=
    ∃up:f<K,∀N p(live:K≤N),
    let L:=fun i=>(books (ρ i)).rows (d i)
    let j:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
    ∃(first:∀i b,j i b≤f)(axes:(i:I)→Bool→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val),
      (∀i (mode b:Bool),Fixed R (d i).val (j i b) target N p f K (e i) (first i b) up.le live
        (((L i).arm b (field i (ρ i) mode b)).source (N,p)) (M i) (ceiling*(β K)^power) (axes i b)) ∧
      (∀i b old (η:ℝ) (A:(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val) x,
        Arrived R (d i).val (j i b) K N p old ((first i b).trans up.le) live η A x →
        A.symm x=(axes i b).symm x) ∧
      Gallery F D T h t d books ρ f N p (up.trans_le live)


omit [Fintype I] [DecidableEq I] [Nonempty I] in
/-- Both source presentations are measured against one native matrix at their
station. Its inverse also acts on any previously admitted single column there. -/
theorem original {D T h t:ℕ}{d:I→Fin (D+1)}{e:I→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:I→ℝ}{cap:ℝ}{power target:ℕ}{ρ:I→{s:ℝ // 0<s ∧ s<δ}}{f K:ℕ}
    (lower:∀i b,(C).ref (d i).val≤WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) b)
    (bought:Delivery F D T h t d e books field M cap power target ρ f K):
    Pinned F D T h t d e books field M cap power target ρ f K:=by
  obtain ⟨up,invoice⟩:=bought
  refine ⟨up,?_⟩
  intro N p live L j
  obtain ⟨first,axes,bounds,house⟩:=invoice N p live
  refine ⟨first,(fun i b=>axes i false b),?_,?_,house⟩
  · intro i mode b
    exact WilsonReflectedMixedPresoldTrial.complete R (lower i b) (bounds i mode b) (bounds i false b).1
  · intro i b old η A x previous
    exact WilsonReflectedMixedIntrinsicAxis.original R (lower i b) ((first i b).trans up.le) live
      previous (bounds i false b).1

omit [DecidableEq I] in
theorem dated (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) →
      (∃i,(ρ i).val=r) →∀i b,
      (C).ref (d i).val≤WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) b:=by
  classical
  let gate:=univ.sup fun i:I=>(C).ref (d i).val
  filter_upwards [WilsonAddressedMixedStationRange.original F simple bliss slow D T h gate d books] with r openAt
  intro ρ span near i b
  have low:(C).ref (d i).val≤gate:=Finset.le_sup (f:=fun k:I=>(C).ref (d k).val) (mem_univ i)
  exact low.trans (((openAt ρ span near).2 i b).1)

end YM.Integration.WilsonReflectedMixedSharedAxis
end
