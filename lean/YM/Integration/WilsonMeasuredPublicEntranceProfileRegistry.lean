import YM.Integration.WilsonMeasuredPublicEntranceSchoolProfile
import YM.Integration.WilsonMeasuredPublicEntranceHeldSchoolProfile
/-! A single elected matrix and an honest complete source panel at each occupied cell serve both fixed-flat and nonconstant physical readings. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceProfileRegistry
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
open WilsonOriginalNullOriginGridRoster (ancestry)
open WilsonMeasuredPublicEntranceHeldCells (Eligible)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open WilsonThermometerUnitFilingCoarse
open PertExtension PertExtension.LatticePT

def Billed {k:ℕ}(φ:Test k)(a scale:ℝ)(side:Side)(err:Sites side k→ℂ)(cost:ℝ):Prop:=
  φ.applyTo (fun x=>err (atSite a scale side x))=∑cell,mass φ a scale side cell*err cell ∧
    ‖φ.applyTo (fun x=>err (atSite a scale side x))‖≤(∫x,‖φ x‖)*cost

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem original {D T t:ℕ}{d:I→Fin (D+1)}{e:I→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:I→ℝ}{E:I→ℕ}{tuition:ℝ}{power target:ℕ}{ρ:I→{s:ℝ // 0<s ∧ s<δ}}{f K:ℕ}
    (one:∀i,1≤M i)(campus:School F D T t d e books field M E tuition power target ρ f K):
  ∃up:f<K,∃electrode:(per:ℕ)→(i:I)→Bool→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val,
  (∀per i b old (η:ℝ) (A:(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val) x
    (before:WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) b≤K),
    Arrived R (d i).val _ K K per old before le_rfl η A x → A.symm x=(electrode per i b).symm x) ∧
  ∀N per (live:K≤N),
    let L:=fun i=>(books (ρ i)).rows (d i)
    let j:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
    ∃ (V:(a:Fin (D+1))→Sight C a.val per)(u:(a:Fin (D+1))→Emblems C a.val)
      (home:∀a:Fin (D+1),Opened C a.val f per),
    (∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N per a.val
      (digits R N per 0) (V a) (u a)) ∧
    ∀n (select:Fin n→I) (mode branch:Fin n→Bool),
      let g:=fun v=>(d (select v)).val
      let Y:=fun v=>((L (select v)).arm (branch v) (field (select v) (ρ (select v)) (mode v) (branch v))).source (N,per)
      ∀(old:Filed R g K),
      let file:=WilsonMeasuredPublicEntranceCutoffFile.complete R g old (fun p v=>electrode p (select v) (branch v))
      file.station=(fun v=>j (select v) (branch v)) →
      ∀requested,(∀v,accuracy g requested v≤e (select v)) →
      ∀k (φ:Test k)(scale:ℝ)(turn:Sites ((C).side f per) k→Fin n→Motion)
        (place:Sites ((C).side f per) k→Fin n→Site ((C).side f per)),
      let Active:={cell:Sites ((C).side f per) k // mass φ ((C).S.a f) scale ((C).side f per) cell≠0}
      (∀cell:Active,∀v w:Fin n,v≠w→((P).budget f).B^2<separation (place cell.val v) (place cell.val w)) →
      ∃panel:Active→Panel R g N per f K up.le live requested power t (capital R D tuition),
        (∀cell:Active,(panel cell).slot=file.station ∧ (panel cell).axis=file.A N per ∧
          (panel cell).names=Y ∧ (panel cell).M=M∘select ∧ (panel cell).turn=turn cell.val ∧
          (panel cell).loc=place cell.val ∧ (panel cell).sensors=(fun v=>V (d (select v))) ∧
          (panel cell).stamps=(fun v=>u (d (select v))) ∧ (panel cell).home=(fun v=>home (d (select v)))) ∧
        ∀(s:(Stock.census (Fin n)).Mode)(desired:ℕ),desired+∑v∈s.val,E (select v)≤requested →
        let cost:=(∏v∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (g v) (M (select v)))*((β f)^desired)⁻¹
        (∀(ear:ℕ)(below:ear≤f),(∀cell,WilsonMeasuredPublicEntrancePanel.Reading R g (panel cell) below) →
          Billed φ ((C).S.a f) scale ((C).side f per)
            (fun cell=>WilsonMeasuredPublicEntranceCellWords.difference R g file up.le live (below.trans up.le)
              Y (turn cell) (place cell) s) cost) ∧
        (∀(ear:ℕ)(below:ear≤f)(W:Sites ((C).side f per) k → Config G ((C).side ear per)),
          (∀cell:Active,WilsonOriginalMicroscopicEntranceHeldMasterRead.ReadingAt R g (panel cell) below (W cell.val)) →
          Billed φ ((C).S.a f) scale ((C).side f per)
            (fun cell=>WilsonMeasuredPublicEntranceHeldCells.difference R g file up.le live (below.trans up.le)
              Y (turn cell) (place cell) s (W cell)) cost):=by
  obtain ⟨up,electrode,locked,issue⟩:=campus
  refine ⟨up,electrode,locked,?_⟩
  intro N per live L slots
  obtain ⟨sensors,stamps,home,enrolled,issued⟩:=issue N per live
  refine ⟨sensors,stamps,home,enrolled,?_⟩
  intro n select mode branch g Y old file stations requested fit k φ scale turn place Active apart
  let paid(cell:Active):=issued n select mode branch old stations requested fit
    (turn cell.val) (place cell.val) (apart cell)
  let panel(cell:Active):Panel R g N per f K up.le live requested power t (capital R D tuition):=(paid cell).choose
  have details(cell:Active):= (paid cell).choose_spec
  refine ⟨panel,?_,?_⟩
  · intro cell
    obtain ⟨station,axes,names,salary,_,_,phase,located,v,pupil,housed,_,_⟩:=details cell
    exact ⟨station,axes,names,salary,phase,located,v,pupil,housed⟩
  intro s desired exposure cost
  have wages(v:Fin n):0≤WilsonAddressedHomeDose.ceiling (R:=R) (g v) (M (select v)):=by
    apply le_trans _ (le_max_left ..)
    exact mul_nonneg zero_le_two (zero_le_one.trans (one _))
  have pos:0≤cost:=mul_nonneg (prod_nonneg fun v _=>wages v)
    (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans ((P).fits.delayed f).le) _))
  constructor
  · intro ear below hearing
    apply WilsonMeasuredPublicEntranceCellWords.profile R g φ scale file up.le live (below.trans up.le)
      Y turn place s cost pos
    intro cell active
    let index:Active:=⟨cell,active⟩
    obtain ⟨station,axes,names,salary,_,_,phase,located,_,_,_,refs,fare⟩:=details index
    have base(v:Fin n):1≤(panel index).M v:=by
      change 1≤(paid index).choose.M v
      rw [salary]
      exact one _
    have sale:=WilsonMeasuredPublicEntranceCellWords.paid R g (panel index) file station axes below
      (hearing index) base (fun v=>E (select v)) refs fare s desired exposure
    dsimp only [panel] at sale
    rw [names,phase,located,salary] at sale
    exact sale
  · intro ear below W hearing
    apply WilsonMeasuredPublicEntranceHeldCells.profile R g φ scale file up.le live (below.trans up.le)
      Y turn place W s cost pos
    intro cell active
    let index:Active:=⟨cell,active⟩
    obtain ⟨station,axes,names,salary,_,_,phase,located,_,_,_,refs,fare⟩:=details index
    have base(v:Fin n):1≤(panel index).M v:=by
      change 1≤(paid index).choose.M v
      rw [salary]
      exact one _
    have sale:=WilsonMeasuredPublicEntranceHeldCells.paid R g (panel index) file station axes below
      (W cell) (hearing index) base (fun v=>E (select v)) refs fare s desired exposure
    dsimp only [panel] at sale
    rw [names,phase,located,salary] at sale
    exact sale

end YM.Integration.WilsonMeasuredPublicEntranceProfileRegistry
end
