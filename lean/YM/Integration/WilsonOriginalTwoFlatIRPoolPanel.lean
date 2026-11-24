import YM.Integration.WilsonOriginalObservedRoseVanePurse
import YM.Integration.WilsonOriginalTwoFlatIRPoolBook
import YM.Integration.WilsonPhysicalMovingForkPinnedMaster
import YM.Integration.WilsonMeasuredPublicEntranceFullCampus
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolPanel
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
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ → tower S)(Z:WilsonPrescription G)

open WilsonPositionThermometerGradedSource
local notation "heads" => source (C) (Finset.univ:Finset (Fin 3))
local notation "SiteSet" => {s:Finset (Fin 3)//s.Nonempty}

open WilsonPositionThermometerCapStation (Group)
open WilsonOriginalTwoFlatRoseNominated (face)
open WilsonOriginalTwoFlatRosePhase (fields)

open WilsonOriginalTwoFlatRoseBook (group)
open WilsonThermometerAlignedCells (atOrigin)
open WilsonOriginalTwoFlatRoseNominated (face)

open WilsonOriginalTwoFlatRoseRelativePhase (nodes recenter translated)

open WilsonMovingForkOpticalBook (reporter)
open WilsonOriginalTwoFlatIRSocketHeardCell (row incumbent held)
open WilsonOriginalTwoFlatIRPoolOrigins (home)
open WilsonReceivedChronologicalFixedRoseVariation (cells)

open WilsonPositionThermometerConnected (value)
open WilsonReceivedChronologicalFixedRoseVariation (signed)

open WilsonMeasuredPublicEntrancePanel (Panel accuracy)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalTwoFlatIRPoolBook (direct)
open WilsonMovingForkPrintedFile (Program)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonOriginalObservedRoseVanePurse (ages)

/-- The N-born pooled name, its own paid home, and the trial matrix are common
to every supported cell. The complete chronological row may be prescribed at K
before the original UV and period regulators. -/
theorem on_course {T h t f K power target:ℕ}{δ tuition:ℝ}{e E:Fin 3→ℕ}{M:Fin 3→ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (ρ:Fin 3→{s:ℝ//0<s ∧ s<δ})(x:∀i:Fin 3,RG17.Free C (grade i).val)
    (extra:∀i:Fin 3,(Spin.comparator (C).book).Field (grade i).val)
    (pinned:WilsonReflectedMixedSharedAxis.Pinned F 6 T h t grade e books
      (WilsonReflectedMixedMasterSchool.field F Jr Z 6 T grade extra x books) M tuition power target ρ f K)
    (school:WilsonMeasuredPublicEntranceFullCampus.School F 6 T t grade e books
      (WilsonReflectedMixedMasterSchool.field F Jr Z 6 T grade extra x books) M E tuition power target ρ f K)
    (program:Program R ages K):
    ∃fk:f<K,∃file:Filed R ages K,
    (∀i,file.station i=(home F Jr Z (books (ρ i)) (grade i) (x i)).j) ∧ file.target=target ∧
    (∀N per w pins j,j<K → file.row N per w pins j=WilsonMovingForkPrintedFile.row program N per w pins j) ∧
    ∀N per (kn:K≤N)(φ:Test 3)(r:ℝ)(requested:ℕ),
    (∀i,accuracy ages requested i≤e i) →
    (∀o:cells R φ r (f,per),∀i k:Fin 3,i≠k → ((P).budget f).B^2<separation (o.val i) (o.val k)) →
    ∃panel:cells R φ r (f,per)→Panel R ages N per f K fk.le kn requested power t (capital R 6 tuition),
    ∀o,(panel o).slot=file.station ∧ (panel o).axis=file.A N per ∧ (panel o).M=M ∧
      (panel o).loc=o.val ∧ (panel o).turn=(fun _=>direct) ∧
      (∀i,(panel o).names i=(home F Jr Z (books (ρ i)) (grade i) (x i)).arm.source (N,per)) ∧
      (∀i,displayed R (ages i) ((panel o).names i) ((panel o).turn i)=
        (home F Jr Z (books (ρ i)) (grade i) (x i)).arm.source (N,per)) ∧
      (∀i k,k≤ages i → (C).ref k≤N) ∧
      (∀i,Next.Rank.Spindle.paid (C) (ages i) f N per ((panel o).names i)≤(panel o).M i*(β f)^(E i)):=by
  classical
  obtain ⟨fk,_,_,_,grant⟩:=WilsonPhysicalMovingForkPinnedMaster.original F pinned
  obtain ⟨old,stations,aim,_,rows⟩:=grant (n:=3) id (fun _=>false) program
  obtain ⟨_,electrode,_,campus⟩:=school
  let file:Filed R ages K:=WilsonMeasuredPublicEntranceCutoffFile.complete R ages old (fun per i=>electrode per i false)
  have origin(i:Fin 3):file.station i=(home F Jr Z (books (ρ i)) (grade i) (x i)).j:=by
    rw [show file.station i=old.station i from rfl,congrFun stations i]
    exact (WilsonMovingForkSlotDate.source F (books (ρ i)) (grade i) (homogeneous F Jr Z (ρ i).val (grade i).val (x i))).1.symm
  refine ⟨fk,file,origin,aim,?_,?_⟩
  · intro N per w pins j past
    change dite (j=K) _ (fun _=>old.row N per w pins j)=_
    rw [dif_neg (Nat.ne_of_lt past)]
    exact congrFun (congrFun (congrFun (congrFun (congrFun rows N) per) w) pins) j
  · intro N per kn φ r requested budget seated
    obtain ⟨_,_,_,_,mounted⟩:=campus N per kn
    let Y(i:Fin 3):=(home F Jr Z (books (ρ i)) (grade i) (x i)).arm.source (N,per)
    have supply(o:cells R φ r (f,per)):=mounted 3 id (fun _=>true) (fun _=>false) old stations requested
      budget (fun _=>direct) o.val (seated o)
    choose panels seating using supply
    refine ⟨panels,?_⟩
    intro o
    obtain ⟨slots,axes,names,cash,_,_,turn,located,_,_,_,refs,fee⟩:=seating o
    have named(i:Fin 3):(panels o).names i=Y i:=by
      rw [congrFun names i]
      exact (congrArg (fun a₀=>a₀.source (N,per))
        (WilsonMovingForkSlotDate.source F (books (ρ i)) (grade i) (homogeneous F Jr Z (ρ i).val (grade i).val (x i))).2).symm
    exact ⟨slots,axes,cash,located,turn,named,fun i=>by
      rw [turn];exact (WilsonOriginalTwoFlatIRPoolBook.target (R:=R) _ _).trans (named i),refs,fee⟩

end YM.Integration.WilsonOriginalTwoFlatIRPoolPanel
end
