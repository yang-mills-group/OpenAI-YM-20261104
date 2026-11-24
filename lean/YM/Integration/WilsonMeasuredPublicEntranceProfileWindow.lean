import YM.Integration.WilsonMeasuredPublicEntranceSchoolProfile
import YM.Integration.WilsonMeasuredPublicEntranceAllCutoffs
import YM.Integration.WilsonSeparatedPrefixGridGround
/-! The entire signed rough-to-independent entrance on the physical precontact interval, against a correlated smooth profile on its actual occupied cells. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceProfileWindow
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

open WilsonReflectedMixedLocatedSchool (Paid)
open WilsonReflectedMixedSharedAxis (Pinned)
open WilsonMeasuredPublicEntranceAllCutoffs (Registered)
open Extraction WilsonAddressedPhysicalCells
open WilsonMeasuredPublicEntranceCellWords (difference)
open WilsonInvariantActionPosition (berth)

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h t:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ //0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (program:Registered F D T h t d books field){Lwidth η:ℝ}(lp:0<Lwidth)(ep:0<η):
    ∃M:I→ℝ,∃E:I→ℕ,(∀i,1≤M i) ∧
    ∀(e:I→ℕ)(pwr _target:ℕ),(∀i,e i+1≤2*pwr) →
    let reserve:=depth ((2*pwr+∑i,E i)+1) (width T h) D
    let cap:=max 1 (4*∑i,M i)
    let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h reserve D
    ∀b:ℕ,h≤b → ∃apron:ℕ,∀floor:ℕ,∀ᶠr in trail,∀ρ:I→{s:ℝ //0<s ∧ s<δ},
    (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) → (∃i,(ρ i).val=r) →
    let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
    let f:=berth R 5 m
    let K:=berth R reserve f
    let L:=fun i=>(books (ρ i)).rows (d i)
    let slots:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
    ∃j:ℕ,floor≤j ∧ j+2≤f ∧ ∃up:f<K,
    ∃electrode:(per:ℕ)→(i:I)→Bool→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val,
    ∀(N per:ℕ)(live:K≤N)(n:ℕ)(select:Fin n→I)(mode branch:Fin n→Bool),
    let g:=fun v=>(d (select v)).val
    let Y:=fun v=>((L (select v)).arm (branch v) (field (select v) (ρ (select v)) (mode v) (branch v))).source (N,per)
    ∀(old:Filed R g K),
    let file:=WilsonMeasuredPublicEntranceCutoffFile.complete R g old (fun p v=>electrode p (select v) (branch v))
    file.station=(fun v=>slots (select v) (branch v)) →
    ∀(requested:ℕ),(∀v,accuracy g requested v≤e (select v)) →
    ∀(base u first:ℕ),first≤floor →
    ReadAt R g base N per apron requested t reserve power (capital R D cap) first →
    base≤u → u≤j → Opened (C) 0 u per → Opened (C) 0 j per →
    ∀k (φ:Test k)(scale:ℝ)
      (turn:Sites ((C).side f per) k→Fin n→Motion)
      (site:Sites ((C).side f per) k→Fin n→Lattice.Cover),
    (∀cell,mass φ ((C).S.a f) scale ((C).side f per) cell≠0 →
      (∀i,‖(C).S.gridPoint f (site cell i)‖≤Lwidth*outer z b r) ∧
        Pairwise fun i k=>η*r≤‖(C).S.gridPoint f (site cell i)-(C).S.gridPoint f (site cell k)‖) →
    ∀(s:(Stock.census (Fin n)).Mode)(desired:ℕ),desired+∑v∈s.val,E (select v)≤requested →
    ∀road:u≤K,
    let debit:=fun cell=>difference R g file up.le live road Y (turn cell) (snap (C) f per (site cell)) s
    let node:=atSite ((C).S.a f) scale ((C).side f per)
    let cost:=(∏v∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (g v) (M (select v)))*((β f)^desired)⁻¹
    φ.applyTo (fun x=>debit (node x))=∑cell,mass φ ((C).S.a f) scale ((C).side f per) cell*debit cell ∧
      ‖φ.applyTo (fun x=>debit (node x))‖≤(∫x,‖φ x‖)*cost:=by
  classical
  obtain ⟨M,E,one,bearing⟩:=program
  refine ⟨M,E,one,?_⟩
  intro e pwr target depthPaid reserve cap power b hb
  obtain ⟨apron,housed⟩:=WilsonSeparatedPrefixGridGround.original F simple bliss slow D T b d books lp ep
  refine ⟨apron,?_⟩
  intro floor
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have grow:∀ᶠr in trail,outer z h r≤outer z b r:=by
    filter_upwards [link.positive,(link.conforms simple).eventually (ge_mem_nhds zero_lt_one),
      self_mem_nhdsWithin (a:=0)] with r gp small positive
    have ratio:1≤(wilson z r)⁻¹:=by
      rw [le_inv_comm₀ zero_lt_one gp]
      simpa only [inv_one] using small
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ratio hb) (le_of_lt positive)
  have placed:=WilsonAddressedMixedStationRange.original F simple bliss slow D T h floor d books
  filter_upwards [bearing e pwr target depthPaid,housed floor,placed,grow] with r enrolled housing margins wider
  intro ρ band near m f K L slots
  obtain ⟨_,_,_,campus⟩:=enrolled ρ band near
  obtain ⟨j,threshold,height,seated⟩:=housing ρ (fun i=>⟨(band i).1,(band i).2.trans wider⟩) near
  obtain ⟨up,electrode,earned⟩:=WilsonMeasuredPublicEntranceSchoolProfile.original F one campus
  refine ⟨j,threshold,height,up,electrode,?_⟩
  intro N per live n select mode branch g Y old file locked requested fit base u first originalGate
    read baseU uj firstEar lastEar k φ scale turn site active s desired exposure road
  have dates(v:Fin n):first≤file.station v:=by
    rw [locked]
    exact originalGate.trans ((margins ρ band near).2 (select v) (branch v)).1
  apply earned N per live n select mode branch old locked requested fit base j u apron reserve first read
    (originalGate.trans threshold) (baseU.trans uj) height rfl dates baseU uj firstEar lastEar k φ scale turn
    (fun cell=>snap (C) f per (site cell)) _ s desired exposure road
  intro cell supported
  rcases isEmpty_or_nonempty (Fin n) with void|residents
  · exact Or.inl (fun v=>void.false v)
  · letI:=residents
    obtain ⟨reach,clear⟩:=active cell supported
    exact Or.inr (seated (Fin n) N per (up.le.trans live) (site cell) reach clear).1

end YM.Integration.WilsonMeasuredPublicEntranceProfileWindow
end
