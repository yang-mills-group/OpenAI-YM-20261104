import YM.Integration.WilsonSeparatedPrefixPanelWord
import YM.Integration.WilsonSeparatedPrefixGridGround
import YM.Integration.WilsonMeasuredPublicEntrancePanelSchool

/-! The full charged upper comparison for the actual fixed public optical file, at every originally screened position. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixSchoolHearing
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

open WilsonMeasuredPublicEntrancePanel (accuracy Panel)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonReflectedMixedSharedAxis (Pinned)
open WilsonReflectedMixedLocatedSchool (Paid)
open WilsonMovingForkHeterogeneousCut (Filed)

open WilsonMeasuredPublicEntrancePanelCampus (School)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonMovingForkMixedSeed (doses product)
open WilsonMovingForkSeededPoint (seats)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open RG16 RG16.Literal

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem original {D T t:ℕ}{d:I→Fin (D+1)}{e:I→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {field:(i:I)→{s:ℝ //0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:I→ℝ}{E:I→ℕ}{tuition:ℝ}{power target:ℕ}{ρ:I→{s:ℝ //0<s ∧ s<δ}}{f K:ℕ}
    (one:∀i,1≤M i)(campus:School F D T t d e books field M E tuition power target ρ f K):
    ∃up:f<K,∀N per (live:K<N),
    let L:=fun i=>(books (ρ i)).rows (d i)
    let slots:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
    ∀n (select:Fin n→I)(mode branch:Fin n→Bool),
    let g:=fun v=>(d (select v)).val
    let Y:=fun v=>((L (select v)).arm (branch v) (field (select v) (ρ (select v)) (mode v) (branch v))).source (N,per)
    ∀(file:Filed R g K),file.station=(fun v=>slots (select v) (branch v)) →
    ∀(desired requested:ℕ),(∀v,accuracy g requested v≤e (select v)) →
    desired+(∑v,E (select v))≤requested →
    ∀(base j u apron reserve first:ℕ),
    ReadAt R g base N per apron requested t reserve power (capital R D tuition) first →
    first≤j → base≤j → j+2≤f → K=WilsonInvariantActionPosition.berth R reserve f →
    (∀v,first≤file.station v) → base≤u → u≤j → Opened (C) 0 u per → Opened (C) 0 j per →
    ∀site:Fin n→Lattice.Cover, ((Fin n)→False) ∨ Ground R N per j f apron (snap (C) f per site) →
    let pin:=seats (R:=R) up.le per site
    let q:=doses R g file.station (N:=N) (per:=per) (file.A N per) Y
    ∀road:u≤K,
    ‖reading R (N:=N) (credit (C) N per 0 (word R g f N per (up.le.trans live.le) site Y) K live.le) u road-
      reading R (N:=N) (numerator R N per K (product R g (N:=N) pin q)) u road‖
      ≤(∏v,WilsonAddressedHomeDose.ceiling (R:=R) (g v) (M (select v)))*((β f)^desired)⁻¹:=by
  obtain ⟨up,issued⟩:=campus
  refine ⟨up,?_⟩
  intro N per live L slots
  obtain ⟨V,emblems,home,_,funded⟩:=issued N per live
  intro n select mode branch g Y file station desired requested order exposure base j u apron reserve first
    read deep baseJ height berth allSlots baseU old earJ earF site ground pin q road
  let o:=snap (C) f per site
  have apart(i k:Fin n)(ne:i≠k):((P).budget f).B^2<separation (o i) (o k):=by
    rcases ground with vacant|purchased
    · exact (vacant i).elim
    · have eqP:((C).path.rep N per f).p=(P).budget f:=
        (R.makes.wilson.represents N per f (up.le.trans live.le)).vac
      have separated:=purchased.2.1 i k ne
      rw [eqP] at separated
      exact separated
  obtain ⟨A,atSlot,axis,rows,fund,_,_,turn,where_,_,_,_,refs,fare⟩:=
    funded n select mode branch file station requested order (fun _=>(1,false)) o apart
  have wageA (v:Fin n):1≤A.M v:=by rw [fund];exact one (select v)
  have paid:=WilsonSeparatedPrefixPanelWord.original R g A site file Y rows where_ turn
    read deep baseJ height berth allSlots ground baseU old earJ earF atSlot axis wageA
    (fun v=>E (select v)) refs fare desired exposure
  dsimp only at paid
  rw [fund] at paid
  exact paid

end YM.Integration.WilsonSeparatedPrefixSchoolHearing
end
