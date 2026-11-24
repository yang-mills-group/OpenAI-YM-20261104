import YM.Integration.WilsonAddressedMixedStationRange
import YM.Integration.WilsonReflectedPublicOpticalJoint
import YM.Integration.WilsonMeasuredPublicEntranceHeadBoard
import YM.Integration.WilsonAddressedPublicGridRooms
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonAddressedMixedStationEstate
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

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(D:ℕ):
    ∃t≥D+3,∀(T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val),
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let j:=berth R 5 m
      ∀p N(deep:j<N),
      ∃ (V:(a:Fin (D+1))→Sight C a.val p)(u:(a:Fin (D+1))→Emblems C a.val)
        (est:∀a:Fin (D+1),Opened C a.val j p),
      (∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) j N p a.val
        (digits R N p 0) (V a) (u a)) ∧
      ∀ (branch:I→Bool)(v:(i:I)→S.Field (d i).val) (c:I→Site ((C).side j p))(names:Census I),
      (∀i k:I,i≠k→((P).budget j).B^2<separation (c i) (c k)) →
      let L:=fun i=>(books (ρ i)).rows (d i)
      let x:=fun i=>((L i).arm (branch i) (v i)).source (N,p)
      let y:=fun i=>offer R (x i) (est (d i)) deep.le
      let data:=fun i=>reduce (y i)
      let b:=fun i=>((C).S.toDepth deep.le p).embed (c i)
      (∀i,WilsonThermometerMarchSource.charge (y i) ≤ max 1
        (2*(β j)^(WilsonAddressedMixedStationRange.width T h*((d i).val+1))*fee F (L i) (branch i) (v i))) ∧
      (∀turn:I→Motion,
        WilsonThermometerReflectedRoster.filed R (fun i=>(d i).val) (fun _=>0) turn c data
          (fun i=>V (d i)) (fun i=>u (d i)) names deep.le t ∧
        ∀e (hj:e ≤ N)(s:names.Mode) U,
          (WilsonThermometerReflectedRoster.density R (fun i=>(d i).val) (fun _=>0) turn c data
            (fun i=>u (d i)) names deep.le hj U).part s =
          ((C).path.rep N p e).eval U • actualTransport C (N:=N)
            (fun W=>∏i∈s.val, ((WilsonThermometerMarchSource.charge (y i):ℝ):ℂ)⁻¹*
              (C).O N p (WilsonReflectedPublicOrientedFaces.displayed R (d i).val (x i) (turn i)) (b i) W) hj U) ∧
      Income R (fun i=>(d i).val) (fun _=>0) c data (fun i=>V (d i)) (fun i=>u (d i))
        names deep t (fun i W=>((WilsonThermometerMarchSource.charge (y i):ℝ):ℂ)⁻¹*(C).O N p (x i) (b i) W):=by
  classical
  obtain ⟨t,degree,market⟩:=WilsonReflectedPublicChargedRoster.original R simple shop D
  have growing:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate (C).path.levels simple)
  obtain ⟨gate,invoice⟩:=eventually_atTop.mp (market.and (growing.eventually_ge_atTop (3:ℝ)))
  refine ⟨t,degree,?_⟩
  intro T h d δ books
  filter_upwards [WilsonAddressedMixedStationRange.original F simple bliss slow D T h gate d books] with r bought
  intro ρ span near m j per N deep
  obtain ⟨wake,homes⟩:=bought ρ span near
  obtain ⟨supply,growth⟩:=invoice j wake
  change 3 ≤ Real.log ((C).path.levels.clock.hatBeta j) at growth
  have room:5 ≤ ((C).path.levels.budget j).B:=by
    have cap:(Real.log ((C).path.levels.clock.hatBeta j))^2 ≤ ((((C).path.levels.budget j).B:ℕ):ℝ):=Nat.le_ceil _
    exact_mod_cast (show (5:ℝ) ≤ ((((C).path.levels.budget j).B:ℕ):ℝ) by
      nlinarith only [cap,growth,sq_nonneg (Real.log ((C).path.levels.clock.hatBeta j)-3)])
  have vac:((C).path.rep N per j).p=(C).path.levels.budget j:=(R.makes.wilson.represents N per j deep.le).vac
  obtain ⟨V,u,est,enrolled,shelf⟩:=supply per N deep
  refine ⟨V,u,est,enrolled,?_⟩
  intro branch v c names gap L x y data b
  have geo (turn:I→Motion)(i k:I)(apart:i≠k):((P).budget j).B^2<
      separation (point R (N:=N) 0 (turn i) (c i) j) (point R (N:=N) 0 (turn k) (c k) j):=by
    simpa only [WilsonReflectedPublicOpticalJoint.location R deep.le] using gap i k apart
  have field:=fun turn=>shelf I d x turn c names (geo turn)
  let idle:=fun _:I=>((1,false):Motion)
  obtain ⟨cash,state,faces⟩:=field idle
  refine ⟨?_,?_,?_⟩
  · intro i
    let k:=WilsonReflectedPublicStationFare.station F (L i) (branch i)
    have house:=homes i (branch i)
    have moved:=WilsonReflectedPublicCensusFare.original F (L i) (books (ρ i)).checked
      (branch i) (v i) (p:=per) house.2.1 deep
    have paid:=(WilsonReflectedPublicStationFare.original F (L i) (books (ρ i)).checked (branch i) (v i)).2 N per
      (house.2.1.trans_lt deep)
    have nn:0 ≤ Next.UVStress.quota C (d i).val k N per (x i):=by
      unfold Next.UVStress.quota Labels.Frame.coeffSize;positivity
    have earned:=nonneg_of_mul_nonneg_right (nn.trans paid) (pow_pos ((C).S.a_pos k) (d i).val)
    apply (cash i).trans (moved.trans (max_le_max_left _ ?_))
    apply mul_le_mul_of_nonneg_right _ earned
    rw [pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg ((C).S.a_pos k).le ((C).S.a_pos j).le) house.2.2 _) zero_le_two
  · intro turn
    obtain ⟨_,full,trace⟩:=field turn
    refine ⟨full,?_⟩
    intro e hj s U
    simpa only [WilsonAddressedPublicGridRooms.top R deep.le] using trace e hj s U
  · have refs (i:I)(e:ℕ)(he:e ≤ (d i).val):(C).ref e ≤ N:=(est ⟨e,Nat.lt_of_le_of_lt he (d i).isLt⟩).post.trans deep.le
    have original:=WilsonAddressedPublicOriginalFaces.original R (fun i=>(d i).val) x (fun i=>V (d i)) (fun i=>u (d i))
        (fun i=>est (d i)) deep.le (fun i=>enrolled (d i)) refs c names t state
    apply WilsonMeasuredPublicEntrancePhysicalHeads.original R (fun i=>(d i).val) (fun _=>0) c data
        (fun i=>V (d i)) (fun i=>u (d i)) names deep t (fun i=>enrolled (d i)) state _ _ (vac.symm ▸ room)
    · simpa only [vac] using geo idle
    · intro s U
      simpa only [WilsonAddressedPublicGridRooms.top R deep.le] using original j deep.le s U

end YM.Integration.WilsonAddressedMixedStationEstate
end
