import YM.Integration.WilsonReflectedMixedSharedAxis
import YM.Integration.WilsonMovingForkPrintedFile

/-! A single fitted matrix for the whole original roster, before the subsets and dated programmes. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalMovingForkPinnedMaster
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
open WilsonReflectedMixedSharedAxis (Pinned)


open WilsonReflectedMixedMasterAxes (Fixed)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkPrintedFile (Program)

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem original {D T h t:ℕ}{d:I→Fin (D+1)}{e:I→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {read:(i:I)→{s:ℝ //0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:I→ℝ}{cap:ℝ}{power target:ℕ}{ρ:I→{s:ℝ //0<s ∧ s<δ}}{f K:ℕ}
    (pinned:Pinned F D T h t d e books read M cap power target ρ f K) :
    let L:=fun i=>(books (ρ i)).rows (d i)
    let j:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
    ∃(up:f<K)(first:∀i b,j i b≤f)(A:∀_N _per:ℕ,∀(i:I)(_b:Bool),
        (C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val),
      (∀N per(live:K≤N)i mode b,Fixed R (d i).val (j i b) target N per f K (e i)
        (first i b) up.le live (((L i).arm b (read i (ρ i) mode b)).source (N,per))
        (M i) (cap*(β K)^power) (A N per i b)) ∧
      ∀{n:ℕ}(ports:Fin n→I)(weak:Fin n→Bool)
        (programme:Program R (fun a=>(d (ports a)).val) K),
      ∃master:Filed R (fun a=>(d (ports a)).val) K,
        master.station=(fun a=>j (ports a) (weak a)) ∧ master.target=target ∧
        master.A=(fun N per a=>A N per (ports a) (weak a)) ∧
        master.row=WilsonMovingForkPrintedFile.row programme:=by
  classical
  intro L j
  obtain ⟨up,issued⟩:=pinned
  let first:= (issued K 0 (le_refl K)).choose
  let A (N per:ℕ)(i:I)(b:Bool):(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val:=
    if live:K≤N then (issued N per live).choose_spec.choose i b else LinearEquiv.refl ℂ _
  have paid:∀N per(live:K≤N)i mode b,Fixed R (d i).val (j i b) target N per f K (e i)
      (first i b) up.le live (((L i).arm b (read i (ρ i) mode b)).source (N,per))
      (M i) (cap*(β K)^power) (A N per i b):=by
    intro N per live i mode b
    simpa only [A,dif_pos live] using ((issued N per live).choose_spec.choose_spec.1 i mode b)
  refine ⟨up,first,A,paid,?_⟩
  intro n ports weak programme
  let master:Filed R (fun a=>(d (ports a)).val) K:={
    station:=fun a=>j (ports a) (weak a)
    target:=target
    before:=fun a=>(first (ports a) (weak a)).trans up.le
    A:=fun N per a=>A N per (ports a) (weak a)
    arrived:=fun N per live a x=>(paid N per live.le (ports a) false (weak a)).1 x
    row:=WilsonMovingForkPrintedFile.row programme
    seed:=by
      intro N per live w ξ
      funext U
      simp [WilsonMovingForkPrintedFile.row]}
  exact ⟨master,rfl,rfl,rfl,rfl⟩

end YM.Integration.WilsonPhysicalMovingForkPinnedMaster
end
