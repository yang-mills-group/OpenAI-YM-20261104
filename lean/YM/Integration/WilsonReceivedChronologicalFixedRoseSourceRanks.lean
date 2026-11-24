import YM.Integration.WilsonReceivedChronologicalFixedRosePhysicalRanks
import YM.Integration.WilsonOriginalTwoFlatIRPoolRegistered
import YM.Integration.WilsonOriginalTwoFlatIRPoolSites
import YM.Integration.WilsonOriginalTwoFlatIRPoolPanel
import YM.Integration.WilsonMeasuredPublicEntranceAllCutoffs
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseSourceRanks
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


open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonInvariantActionPosition (berth)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonReflectedMixedMasterSchool (field)

open WilsonReceivedChronologicalFixedRosePhysicalRanks (entrance)

def request (aim physical:ℕ)(E:Fin 3→ℕ):ℕ:=entrance aim physical+∑i,E i

def debit (aim physical:ℕ)(E:Fin 3→ℕ):ℕ:=∑i:Fin 3,(accuracy ages (request aim physical E) i+1)

theorem share (aim physical:ℕ)(E:Fin 3→ℕ)(s:Finset (Fin 3)):
    entrance aim physical+∑i∈s,E i≤request aim physical E:=
  Nat.add_le_add_left (sum_le_sum_of_subset (subset_univ s)) _

theorem grant (aim physical:ℕ)(E:Fin 3→ℕ)(i:Fin 3):
    accuracy ages (request aim physical E) i+1≤2*debit aim physical E:=by
  have paid:accuracy ages (request aim physical E) i+1≤debit aim physical E:=
    single_le_sum (f:=fun j:Fin 3=>accuracy ages (request aim physical E) j+1) (fun _ _=>Nat.zero_le _) (mem_univ i)
  omega

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {T h t:ℕ}{δ:ℝ}(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(extra:∀i:Fin 3,(Spin.comparator (C).book).Field (grade i).val)
    (registrar:WilsonMeasuredPublicEntrancePanelSchool.Registered F 6 T h t grade books (field F Jr Z 6 T grade extra x books)):
    ∃(M:Fin 3→ℝ)(E:Fin 3→ℕ),(∀i,1≤M i) ∧ ∀φ:Test 3,∃apron:ℕ,∀(aim physical:ℕ),let requested:=request aim physical E
    let pwr:=debit aim physical E
    let τ:=depth ((2*pwr+∑i,E i)+1) (width T h) 6
    let tuition:=max 1 (4*∑i,M i)
    let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h τ 6
    (∀s:Finset (Fin 3),entrance aim physical+∑i∈s,E i≤requested) ∧
    ∀(floor target:ℕ),∀ᶠr in trail,∀ρ:Fin 3→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    let K:=berth R τ f
    ∃j:ℕ,floor≤j ∧ j+2≤f ∧ ∀program:Program R ages K,
    ∃fk:f<K,∃file:Filed R ages K,
    (∀i,file.station i=(home F Jr Z (books (ρ i)) (grade i) (x i)).j) ∧ file.target=target ∧
    (∀N per w pins j,j<K → file.row N per w pins j=WilsonMovingForkPrintedFile.row program N per w pins j) ∧
    ∀N per (kn:K≤N),
    ∃panel:cells R φ r (f,per)→Panel R ages N per f K fk.le kn requested power t (capital R 6 tuition),
    ∀o,Ground R N per j f apron o.val ∧ (panel o).slot=file.station ∧ (panel o).axis=file.A N per ∧ (panel o).M=M ∧
      (panel o).loc=o.val ∧ (panel o).turn=(fun _=>direct) ∧
      (∀i,(panel o).names i=(home F Jr Z (books (ρ i)) (grade i) (x i)).arm.source (N,per)) ∧
      (∀i,displayed R (ages i) ((panel o).names i) ((panel o).turn i)=
        (home F Jr Z (books (ρ i)) (grade i) (x i)).arm.source (N,per)) ∧
      (∀i k,k≤ages i → (C).ref k≤N) ∧
      (∀i,Next.Rank.Spindle.paid (C) (ages i) f N per ((panel o).names i)≤(panel o).M i*(β f)^(E i)) :=by
  obtain ⟨M,E,one,funding⟩:=WilsonOriginalTwoFlatIRPoolRegistered.original F Jr Z simple bliss slow books x extra registrar
  refine ⟨M,E,one,?_⟩
  intro φ
  obtain ⟨apron,school⟩:=funding φ
  refine ⟨apron,?_⟩
  intro aim physical requested pwr τ tuition power
  refine ⟨share aim physical E,?_⟩
  intro floor target
  filter_upwards [school floor (accuracy ages requested) pwr target (grant aim physical E)] with r bought
  intro ρ span near f K
  obtain ⟨j,late,early,placed⟩:=bought ρ span near
  refine ⟨j,late,early,?_⟩
  intro program
  obtain ⟨fk,file,ports,focus,rows,terms⟩:=placed program
  exact ⟨fk,file,ports,focus,rows,fun N per kn=>terms N per kn requested (fun _=>le_rfl)⟩
end YM.Integration.WilsonReceivedChronologicalFixedRoseSourceRanks
end
