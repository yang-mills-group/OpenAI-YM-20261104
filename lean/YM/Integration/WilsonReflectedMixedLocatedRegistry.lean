import YM.Integration.WilsonSeparatedPrefixScreenedCampus
import YM.Integration.WilsonReflectedMixedLocatedSeats
import YM.Integration.WilsonReflectedMixedSignedCampus
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReflectedMixedLocatedRegistry
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


open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open WilsonReflectedMixedThermalArms (rent)
variable {J:Type}[Fintype J][DecidableEq J]

def Grant (D T t:ℕ)(d:I→Fin (D+1))(choose:J→I)(e:J→ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val)
    (M:I→ℝ)(cap:ℝ)(power target:ℕ)(ρ:I→{s:ℝ // 0<s ∧ s<δ})(f K:ℕ):Prop:=
    let master:=fun i=>(books (ρ i)).rows (d i)
    ∃up:f<K,∀ N p (live:K≤N),
    ∃(V:(a:Fin (D+1))→Sight C a.val p)(u:(a:Fin (D+1))→Emblems C a.val)(home:∀a,Opened C a.val f p),
    (∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p a.val (digits R N p 0) (V a) (u a)) ∧
    ∀(branch:J→Bool)(root:J→Site ((C).side f p))(names:Census J),
      (∀i k:J,i≠k→((P).budget f).B^2<separation (root i) (root k)) →
      let grade:=d∘choose
      let site:=fun i=>(master (choose i)).arm (branch i) (field (choose i) (ρ (choose i)) (branch i))
      let j:=fun i=>WilsonReflectedPublicStationFare.station F (master (choose i)) (branch i)
      let source:=fun i=>(site i).source (N,p)
      let y:=fun i=>offer R (source i) (home (grade i)) (up.le.trans live)
      let data:=fun i=>reduce (y i)
      let bare:=fun i=>((C).S.toDepth (up.le.trans live) p).embed (root i)
      (∀turn:J→Motion,WilsonThermometerReflectedRoster.filed R (fun i=>(grade i).val) (fun _=>0) turn root data
        (fun i=>V (grade i)) (fun i=>u (grade i)) names (up.le.trans live) t ∧
        (∀k (hk:k≤N)(s:names.Mode) U,
          (WilsonThermometerReflectedRoster.density R (fun i=>(grade i).val) (fun _=>0) turn root data
            (fun i=>u (grade i)) names (up.le.trans live) hk U).part s =
          ((C).path.rep N p k).eval U • actualTransport C (N:=N)
            (fun W=>∏i∈s.val,((WilsonThermometerMarchSource.charge (y i):ℝ):ℂ)⁻¹*
              (C).O N p (WilsonReflectedPublicOrientedFaces.displayed R (grade i).val (source i) (turn i)) (bare i) W) hk U) ∧
        ∃(before:∀i,j i≤f)(A:(i:J)→(C).label (grade i).val ≃ₗ[ℂ] (C).label (grade i).val),
        (∀i a,Arrived R (grade i).val (j i) K N p target ((before i).trans up.le) live (1/32) (A i) a) ∧
        ∀i,WilsonReflectedPublicCommonEstate.Ready (R:=R) (e i) (orbitCost ((C).labels.level (grade i).val)*cap)
          power (rent R (grade i).val (M (choose i))) (source i) (j i) 1 (A i)
          (V (grade i)) (u (grade i)) (home (grade i)) up live (turn i) (root i)) ∧
      Income R (fun i=>(grade i).val) (fun _=>0) root data (fun i=>V (grade i)) (fun i=>u (grade i))
        names (up.trans_le live) t (fun i W=>((WilsonThermometerMarchSource.charge (y i):ℝ):ℂ)⁻¹*(C).O N p (source i) (bare i) W)

def Program (D T h t:ℕ)(d:I→Fin (D+1))(choose:J→I)(e:J→ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val)
    (M:I→ℝ)(E:I→ℕ)(pwr target:ℕ):Prop:=
  let τ:=depth ((2*pwr+∑i,E i)+1) (width T h) D
  let cap:=max 1 (4*∑i,M i)
  let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h τ D
  ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) →
    (∃i,(ρ i).val=r) →
    let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
    let f:=berth R 5 m
    let K:=berth R τ f
    let master:=fun i=>(books (ρ i)).rows (d i)
    (∀i b,WilsonReflectedPublicStationFare.fee F (master i) b (field i (ρ i) b)≤M i*(β f)^(E i)) →
    Grant F D T t d choose e books field M cap power target ρ f K

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1≤((P).budget i).supportExponent)
    (caps:∀i,((P).budget i).supportExponent≤100)(quote:OPE.Therm.Poetry (P))(D:ℕ):
    ∃t≥D+3,∀(T h:ℕ)(d:I→Fin (D+1))(choose:J→I)(e:J→ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val)
    (M:I→ℝ)(E:I→ℕ)(_one:∀i,1≤M i)(pwr target:ℕ)(_reserve:∀i,e i+1≤2*pwr),
      Program F D T h t d choose e books field M E pwr target:=by
  classical
  obtain ⟨t,allocated,market⟩:=WilsonSeparatedPrefixScreenedCampus.original (I:=I) F simple bliss slow shop D
  refine ⟨t,allocated,?_⟩
  intro T h d choose e δ books field M E one pwr target reserve
  unfold Program
  intro τ cap power
  obtain ⟨floor,assemble⟩:=WilsonReflectedMixedSignedCampus.original R simple shop (fun i=>(d (choose i)).val) e
  let gate:=max floor (univ.sup fun k:Fin (D+1)=>(C).ref k.val)
  filter_upwards [market T h d books,WilsonReflectedMixedLocatedSeats.original F simple bliss slow shop wide caps quote
    D T h d books field M E one pwr target,WilsonAddressedMixedStationRange.original F simple bliss slow D T h gate d books]
    with r mounted sold later
  intro ρ span near m f K master tariffs
  unfold Grant
  intro fundedMaster
  obtain ⟨up,sit⟩:=sold ρ span near tariffs
  have late:=later ρ span near
  refine ⟨up,?_⟩
  intro N p live
  have deep:f<N:=up.trans_le live
  obtain ⟨V,u,home,enrolled,hearing⟩:=mounted ρ span near p N deep
  refine ⟨V,u,home,enrolled,?_⟩
  intro branch root names apart grade site j source y data bare
  let v:=fun i=>field (choose i) (ρ (choose i)) (branch i)
  have filed:=hearing J choose branch v root names apart
  refine ⟨?_,filed.2.2⟩
  intro turn
  have physical:=filed.2.1 turn
  refine ⟨physical.1,physical.2,?_⟩
  have station(i:J):floor≤j i:=(le_max_left ..).trans ((late.2 (choose i) (branch i)).1)
  have ref(i:J)(k:ℕ)(hk:k≤(grade i).val):(C).ref k≤f:=by
    let k':Fin (D+1):=⟨k,hk.trans_lt (grade i).isLt⟩
    exact (Finset.le_sup (f:=fun x:Fin (D+1)=>(C).ref x.val) (mem_univ k')).trans ((le_max_right ..).trans late.1)
  exact assemble j station ((le_max_left ..).trans late.1) up live source (fun i=>M (choose i))
    (fun i=>zero_le_one.trans (one (choose i))) cap
    (fun i=>sit N p live (choose i) (branch i) (e i) (reserve i))
    (fun i=>V (grade i)) (fun i=>u (grade i)) (fun i=>home (grade i)) (fun i=>enrolled (grade i))
    ref turn root names t physical.1

end YM.Integration.WilsonReflectedMixedLocatedRegistry
end
