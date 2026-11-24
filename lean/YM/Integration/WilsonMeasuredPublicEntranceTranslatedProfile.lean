import YM.Integration.WilsonMeasuredPublicEntranceProfileRegistry
import YM.Integration.WilsonMeasuredPublicEntranceProfileMesh
import YM.Integration.WilsonMeasuredPublicEntranceShiftedSites
/-! Signed joint profiles on independently translated true public sites. The very same cutoff matrix and earned cell panels serve every earlier flat ear and original nonconstant measurement. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTranslatedProfile
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
open WilsonMeasuredPublicEntranceProfileRegistry (Billed)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open WilsonMeasuredPublicEntranceHeldCells (Eligible)
open WilsonOriginalNullOriginGridRoster (ancestry)
open WilsonInvariantActionPosition (berth)

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h t:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ //0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (program:Registered F D T h t d books field):
    ∃M:I→ℝ,∃E:I→ℕ,(∀i,1≤M i) ∧
    ∀(e:I→ℕ)(pwr _target:ℕ),(∀i,e i+1≤2*pwr) →
    let reserve:=depth ((2*pwr+∑i,E i)+1) (width T h) D
    let cap:=max 1 (4*∑i,M i)
    let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h reserve D
    ∀b:ℕ,h≤b → ∀width sep:ℝ,0<width → 0<sep → ∃apron:ℕ,∀floor k:ℕ,∀ᶠr in trail,
    ∀ρ:I→{s:ℝ //0<s ∧ s<δ},
    (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) → (∃i,(ρ i).val=r) →
    let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
    let f:=berth R 5 m
    let K:=berth R reserve f
    let L:=fun i=>(books (ρ i)).rows (d i)
    let slots:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
    ∃j:ℕ,floor≤j ∧ j+2≤f ∧ ∃up:f<K,
∃electrode:(per:ℕ)→(i:I)→Bool→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val,
  (∀per i b old (η:ℝ) (A:(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val) x
    (before:WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) b≤K),
    Arrived R (d i).val _ K K per old before le_rfl η A x → A.symm x=(electrode per i b).symm x) ∧
  ∀N per (live:K≤N),
    ∃ (V:(a:Fin (D+1))→Sight C a.val per)(u:(a:Fin (D+1))→Emblems C a.val)
      (home:∀a:Fin (D+1),Opened C a.val f per),
    (∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N per a.val
      (digits R N per 0) (V a) (u a)) ∧
    ∀n (select:Fin n→I) (mode branch:Fin n→Bool),
      let g:=fun v=>(d (select v)).val
      let Y:=fun v=>((L (select v)).arm (branch v) (field (select v) (ρ (select v)) (mode v) (branch v))).source (N,per)
      ∀(old:Filed R g K),
      let file:=WilsonMeasuredPublicEntranceCutoffFile.complete R g old (fun p v=>electrode p (select v) (branch v))
      file.station=(fun v=>slots (select v) (branch v)) →
      ∀requested,(∀v,accuracy g requested v≤e (select v)) →
      ∀(φ:Test k)(scale:ℝ)(coords:Fin n→Fin k)(origin:Fin n→Lattice.Cover)
        (turn:Sites ((C).side f per) k→Fin n→Motion),
      (∀x:Points k,φ x≠0 →
        let center:=fun v=>(C).S.gridPoint f (origin v)+scale • x (coords v)
        (∀v,‖center v‖≤width*outer z b r) ∧ Pairwise fun v w=>sep*r≤‖center v-center w‖) →
      let place:=fun (cell:Sites ((C).side f per) k) v=>wrap ((C).side f per) (origin v)+cell (coords v)
      let Active:={cell:Sites ((C).side f per) k // mass φ ((C).S.a f) scale ((C).side f per) cell≠0}
      ∃panel:Active→Panel R g N per f K up.le live requested power t (capital R D cap),
        (∀cell:Active,(panel cell).slot=file.station ∧ (panel cell).axis=file.A N per ∧
          (panel cell).names=Y ∧ (panel cell).M=M∘select ∧ (panel cell).turn=turn cell.val ∧
          (panel cell).loc=place cell.val ∧ (panel cell).sensors=(fun v=>V (d (select v))) ∧
          (panel cell).stamps=(fun v=>u (d (select v))) ∧ (panel cell).home=(fun v=>home (d (select v)))) ∧
        ∀(s:(Stock.census (Fin n)).Mode)(desired:ℕ),desired+∑v∈s.val,E (select v)≤requested →
        let cost:=(∏v∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (g v) (M (select v)))*((β f)^desired)⁻¹
        (∀base ear first,first≤floor →
          WilsonMeasuredPublicEntranceMasterUpper.ReadAt R g base N per apron requested t reserve power (capital R D cap) first →
          base≤ear → ear≤j → Opened (C) 0 ear per → Opened (C) 0 j per → ∀road:ear≤K,
          Billed φ ((C).S.a f) scale ((C).side f per)
            (fun cell=>WilsonMeasuredPublicEntranceCellWords.difference R g file up.le live road Y (turn cell) (place cell) s) cost) ∧
        (∀base ear first degree probe,first≤floor →
          WilsonOriginalMicroscopicEntranceHeldMasterUpper.ReadAt R g base N per apron requested t reserve power degree probe (capital R D cap) first →
          base+1≤ear → first≤ear → ear≤f → (j≤ear ∨ (C).S.a ear/(C).S.a f≤(β f)^apron) →
          ∀W:Sites ((C).side f per) k → Config G ((C).side ear per),
          (∀cell:Active,Eligible R (N:=N) degree probe (W cell.val)) → ∀road:ear≤K,
          Billed φ ((C).S.a f) scale ((C).side f per)
            (fun cell=>WilsonMeasuredPublicEntranceHeldCells.difference R g file up.le live road Y (turn cell) (place cell) s (W cell)) cost):=by
  classical
  obtain ⟨M,E,one,bearing⟩:=program
  refine ⟨M,E,one,?_⟩
  intro e pwr target depthPaid reserve cap power b hb width sep wp sp
  obtain ⟨apron,housed⟩:=WilsonSeparatedPrefixGridGround.original F simple bliss slow D T b d books
    (L:=width+1) (by linarith) (η:=sep/2) (half_pos sp)
  refine ⟨apron,?_⟩
  intro floor k
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have grow:∀ᶠr in trail,outer z h r≤outer z b r:=by
    filter_upwards [link.positive,(link.conforms simple).eventually (ge_mem_nhds zero_lt_one),
      self_mem_nhdsWithin (a:=0)] with r gp small positive
    have ratio:1≤(wilson z r)⁻¹:=by
      rw [le_inv_comm₀ zero_lt_one gp]
      simpa only [inv_one] using small
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ratio hb) (le_of_lt positive)
  have placed:=WilsonAddressedMixedStationRange.original F simple bliss slow D T h floor d books
  have mesh:=WilsonMeasuredPublicEntranceProfileMesh.original (I:=I) F simple D T k books
    (t:=min 1 (sep/4)) (lt_min zero_lt_one (by positivity))
  filter_upwards [bearing e pwr target depthPaid,housed floor,placed,grow,mesh,self_mem_nhdsWithin (a:=(0:ℝ))]
    with r enrolled housing margins wider refined rp
  intro ρ band near m f K L slots
  obtain ⟨_,_,_,campus⟩:=enrolled ρ band near
  obtain ⟨j,threshold,height,seated⟩:=housing ρ (fun i=>⟨(band i).1,(band i).2.trans wider⟩) near
  obtain ⟨up,electrode,immutable,sold⟩:=WilsonMeasuredPublicEntranceProfileRegistry.original F one campus
  refine ⟨j,threshold,height,up,electrode,immutable,?_⟩
  intro N per live
  obtain ⟨sensors,stamps,home,prior,openings⟩:=sold N per live
  refine ⟨sensors,stamps,home,prior,?_⟩
  intro n select mode branch g Y old file locked requested levels φ scale coords origin turn support place Active
  have touches:=near
  obtain ⟨i,inner⟩:=touches
  have radius:r≤outer z b r:=inner.symm.le.trans ((band i).2.trans wider)
  have hmesh:4*(k:ℝ)*(C).S.a f ≤ min 1 (sep/4)*r:=refined ρ near
  have small:4*(k:ℝ)*(C).S.a f≤outer z b r:=(hmesh.trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_left 1 (sep/4)) (le_of_lt rp))).trans radius
  have clear:4*(k:ℝ)*(C).S.a f≤(sep/4)*r:=hmesh.trans (mul_le_mul_of_nonneg_right (min_le_right ..) (le_of_lt rp))
  obtain ⟨cover,original,shape⟩:=WilsonMeasuredPublicEntranceShiftedSites.original R φ (per:=per) scale coords origin support small clear
  have grounds(cell:Active):((Fin n)→False) ∨ Ground R N per j f apron (place cell.val):=by
    rcases isEmpty_or_nonempty (Fin n) with void|inhabited
    · exact Or.inl (fun v=>void.false v)
    · letI:=inhabited
      obtain ⟨compact,apart⟩:=shape cell.val cell.property
      have ground:Ground R N per j f apron (snap (C) f per (cover cell.val)):=
        (seated (Fin n) N per (up.le.trans live) (cover cell.val) compact apart).1
      have pin:snap (C) f per (cover cell.val)=place cell.val:=original cell.val
      exact Or.inr (pin ▸ ground)
  have distances(cell:Active):∀v w:Fin n,v≠w→((C).path.rep N per f).p.B^2+1 ≤ separation (place cell.val v) (place cell.val w):=by
    rcases grounds cell with vacant|ground
    · exact fun v=>(vacant v).elim
    · exact ground.2.1
  have apart(cell:Active)(v w:Fin n)(ne:v≠w):((P).budget f).B^2<separation (place cell.val v) (place cell.val w):=by
    have own:=distances cell v w ne
    have given:((C).path.rep N per f).p=(P).budget f:=(R.makes.wilson.represents N per f (up.le.trans live)).vac
    rw [given] at own
    exact own
  obtain ⟨panels,registry,hear⟩:=openings n select mode branch old locked requested levels k φ scale turn place apart
  refine ⟨panels,registry,?_⟩
  intro s desired exposure cost
  obtain ⟨flat,real⟩:=hear s desired exposure
  have gates(first:ℕ)(firstFloor:first≤floor)(cell:Active)(v:Fin n):first≤(panels cell).slot v:=by
    rw [(registry cell).1,locked]
    exact firstFloor.trans ((margins ρ band near).2 (select v) (branch v)).1
  constructor
  · intro base ear first early read baseU uj beginning later road
    have before:ear≤f:=uj.trans ((Nat.le_add_right j 2).trans height)
    apply flat ear before
    intro cell
    have loc: (panels cell).loc=place cell.val:=(registry cell).2.2.2.2.2.1
    exact read j f K (early.trans threshold) (baseU.trans uj) height rfl up.le live (panels cell)
      (gates first early cell) (loc ▸ grounds cell) ear baseU uj beginning later
  · intro base ear first degree probe early read mature begun before optical W eligible road
    apply real ear before W
    intro cell
    have loc: (panels cell).loc=place cell.val:=(registry cell).2.2.2.2.2.1
    let center:=fun _:Unit=>(0:Lattice.Cover)
    have zero:(C).S.gridPoint f (0:Lattice.Cover)=0:=by
      simpa only [sub_self] using Frontier6.Road.grid_sub (C) f (0:Lattice.Cover) 0
    have limit (_:Unit):‖(C).S.gridPoint f (0:Lattice.Cover)‖≤(width+1)*outer z b r:=by
      rw [zero,norm_zero]
      exact mul_nonneg (by linarith only [wp]) ((le_of_lt rp).trans radius)
    have vac:Ground R N per j f apron (snap (C) f per center):=
      (seated Unit N per (up.le.trans live) center limit (fun i a ne=>(ne (Subsingleton.elim i a)).elim)).1
    have span:(C).S.a ear/(C).S.a f≤(β f)^apron:=by
      rcases optical with window|direct
      · exact (div_le_div_of_nonneg_right ((C).S.strictAnti.antitone window) ((C).S.a_pos f).le).trans vac.2.2.1
      · exact direct
    let path:=fun date (i:Unit×((Fin n)×Bool))=>ancestry R per f (place cell.val i.2.1) date
    have guide:=WilsonSeparatedPrefixGridGround.branch (R:=R) (place cell.val)
    have readings:=read ear f K mature begun before rfl up.le live (panels cell) (gates first early cell) path vac.1
      (loc ▸ distances cell) span (loc ▸ guide.1) (fun a _ deep=>guide.2 a deep)
    rcases eligible cell with ⟨openField,spring⟩|⟨wheel,a,test,i,leq,same⟩
    · exact readings.1 _ openField spring
    · rw [same]
      exact readings.2 wheel a test i leq

end YM.Integration.WilsonMeasuredPublicEntranceTranslatedProfile
end
