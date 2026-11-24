import YM.Integration.WilsonMeasuredPublicEntranceFullCampus
import YM.Integration.WilsonMeasuredPublicEntranceCellWords
/-! One preappointed family of public Wilson sources hears every correlated signed finite profile on the same physical and independently measured words. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceSchoolProfile
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

open Extraction WilsonAddressedPhysicalCells
open WilsonMeasuredPublicEntranceFullCampus (School)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonMeasuredPublicEntranceCellWords (difference)
open WilsonThermometerUnitFilingCoarse
open PertExtension PertExtension.LatticePT

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem original {D T t:ℕ}{d:I→Fin (D+1)}{e:I→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:I→ℝ}{E:I→ℕ}{tuition:ℝ}{power target:ℕ}{ρ:I→{s:ℝ // 0<s ∧ s<δ}}{f K:ℕ}
    (one:∀i,1≤M i)(campus:School F D T t d e books field M E tuition power target ρ f K):
    ∃up:f<K,∃electrode:(per:ℕ)→(i:I)→Bool→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val,
    ∀N per (live:K≤N),
    let L:=fun i=>(books (ρ i)).rows (d i)
    let slots:=fun i b=>station F (L i) b
    ∀n (select:Fin n→I) (mode branch:Fin n→Bool),
    let g:=fun v=>(d (select v)).val
    let Y:=fun v=>((L (select v)).arm (branch v) (field (select v) (ρ (select v)) (mode v) (branch v))).source (N,per)
    ∀(old:Filed R g K),
    let file:=WilsonMeasuredPublicEntranceCutoffFile.complete R g old (fun p v=>electrode p (select v) (branch v))
    file.station=(fun v=>slots (select v) (branch v)) →
    ∀(requested:ℕ),(∀v,accuracy g requested v≤e (select v)) →
    ∀(base j u apron reserve first:ℕ),
    ReadAt R g base N per apron requested t reserve power (capital R D tuition) first →
    first≤j → base≤j → j+2≤f → K=berth R reserve f → (∀v,first≤file.station v) →
    base≤u → u≤j → Opened (C) 0 u per → Opened (C) 0 j per →
    ∀k (φ:Test k)(scale:ℝ)
      (turn:Sites ((C).side f per) k→Fin n→Motion)
      (place:Sites ((C).side f per) k→Fin n→Site ((C).side f per)),
    (∀cell,mass φ ((C).S.a f) scale ((C).side f per) cell≠0 →
      ((Fin n)→False) ∨ Ground R N per j f apron (place cell)) →
    ∀(s:(Stock.census (Fin n)).Mode)(desired:ℕ),desired+∑v∈s.val,E (select v)≤requested →
    ∀road:u≤K,
    let debit:=fun cell=>difference R g file up.le live road Y (turn cell) (place cell) s
    let node:=atSite ((C).S.a f) scale ((C).side f per)
    let cost:=(∏v∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (g v) (M (select v)))*((β f)^desired)⁻¹
    φ.applyTo (fun x=>debit (node x))=∑u,mass φ ((C).S.a f) scale ((C).side f per) u*debit u ∧
      ‖φ.applyTo (fun x=>debit (node x))‖≤(∫x,‖φ x‖)*cost:=by
  obtain ⟨up,electrode,_,issue⟩:=campus
  refine ⟨up,electrode,?_⟩
  intro N per live L slots
  obtain ⟨sensors,stamps,home,_,issued⟩:=issue N per live
  intro n select mode branch g Y old file stations requested fit base j u apron reserve first
    purchase deep baseJ height date atSlot baseU uj opening opened k φ scale turn place funds s desired exposure road debit node cost
  have wages(v:Fin n):0≤WilsonAddressedHomeDose.ceiling (R:=R) (g v) (M (select v)):=by
    apply le_trans _ (le_max_left ..)
    exact mul_nonneg zero_le_two (zero_le_one.trans (one _))
  apply WilsonMeasuredPublicEntranceCellWords.profile R g φ scale file up.le live road Y turn place s cost
    (mul_nonneg (prod_nonneg fun v _=>wages v) (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans ((P).fits.delayed f).le) _)))
  intro cell active
  have ground:=funds cell active
  have apart(i a:Fin n)(ne:i≠a):((P).budget f).B^2<separation (place cell i) (place cell a):=by
    rcases ground with none|entered
    · exact (none i).elim
    · have own:=entered.2.1 i a ne
      have equal:((C).path.rep N per f).p=(P).budget f:=(R.makes.wilson.represents N per f (up.le.trans live)).vac
      rw [equal] at own
      exact own
  obtain ⟨A,station,axis,source,cash,_,_,phase,sites,_,_,_,refs,priced⟩:=
    issued n select mode branch old stations requested fit (turn cell) (place cell) apart
  have earned:=purchase j f K deep baseJ height date up.le live A (station ▸ atSlot)
    (sites ▸ ground) u baseU uj opening opened
  have positive(v:Fin n):1≤A.M v:=by rw [cash];exact one _
  have grant:=WilsonMeasuredPublicEntranceCellWords.paid R g A file station axis _ earned positive
    (fun v=>E (select v)) refs priced s desired exposure
  rw [source,phase,sites,cash] at grant
  exact grant

end YM.Integration.WilsonMeasuredPublicEntranceSchoolProfile
end
