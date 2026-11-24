import YM.Integration.WilsonPhysicalMovingForkPinnedMaster
import YM.Integration.WilsonPhysicalAbsoluteVaneCut

/-! The actual registered weak arms on one selected set of stations and their restored finite
K trial in every turned slot of the determining programme. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalAbsoluteVaneMaster
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

open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem original (J:ℝ→tower S)(Z:WilsonPrescription G){D T h t:ℕ}{d:I→Fin (D+1)}
    (glyph:(i:I)→((C).labels.level (d i)).Index)(x:∀i,RG17.Free (C) (d i).val){e:I→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {M:I→ℝ}{cap:ℝ}{power target:ℕ}{ρ:I→{s:ℝ //0<s ∧ s<δ}}{f K:ℕ}
    (pinned:Pinned F D T h t d e books
      (WilsonReflectedMixedMasterSchool.field F J Z D T d (fun i=>WilsonPhysicalVaneBasis.field (C) (d i) (glyph i)) x books)
      M cap power target ρ f K):
    let L:=fun i=>(books (ρ i)).rows (d i)
    let j:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
    ∃(up:f<K)(first:∀i b,j i b≤f)(A:∀_N _per:ℕ,∀(i:I)(_b:Bool),
        (C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val),
      (∀N per(live:K≤N)i,Fixed R (d i).val (j i true) target N per f K (e i)
        (first i true) up.le live (((L i).arm true ((books (ρ i)).V (d i)
          (WilsonPhysicalVaneBasis.field (C) (d i) (glyph i)))).source (N,per))
        (M i) (cap*(β K)^power) (A N per i true)) ∧
      ∀{n:ℕ}(ports:Fin n→I)(programme:Program R (fun a=>(d (ports a)).val) K),
      ∃master:Filed R (fun a=>(d (ports a)).val) K,
        master.station=(fun a=>(books (ρ (ports a))).W.k) ∧ master.target=target ∧
        master.A=(fun N per a=>A N per (ports a) true) ∧
        master.row=WilsonMovingForkPrintedFile.row programme ∧
        ∀(turn:Fin n→Motion)(N per:ℕ)(i:Fin n),
          WilsonPhysicalAbsoluteVaneCut.debit F (fun a=>d (ports a)) (fun a=>books (ρ (ports a)))
              (fun a=>glyph (ports a)) master turn N per i=
            WilsonPhysicalAbsoluteVaneDirections.column F (books (ρ (ports i))) (d (ports i)) N per (glyph (ports i)):=by
  intro L j
  obtain ⟨up,first,A,income,posted⟩:=WilsonPhysicalMovingForkPinnedMaster.original F pinned
  refine ⟨up,first,A,?_,?_⟩
  · intro N per live i
    exact income N per live i false true
  · intro n ports programme
    obtain ⟨master,same,mt,ma,mr⟩:=posted ports (fun _=>true) programme
    refine ⟨master,same,mt,ma,mr,?_⟩
    intro turn N per i
    exact WilsonPhysicalAbsoluteVaneCut.posted F (fun a=>d (ports a)) (fun a=>books (ρ (ports a)))
      (fun a=>glyph (ports a)) master turn N per i (congrFun same i)

end YM.Integration.WilsonPhysicalAbsoluteVaneMaster
