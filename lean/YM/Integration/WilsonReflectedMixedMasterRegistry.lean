import YM.Integration.WilsonSeparatedPrefixScreenedCampus
import YM.Integration.WilsonReflectedMixedLocatedSeats
import YM.Integration.WilsonReflectedMixedMasterAxes
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReflectedMixedMasterRegistry
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

/-- The original physical roster, with all traces and fees under one fixed
choice of sights, emblems and open source pages. -/
def Gallery (D T h t:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (ρ:I→{s:ℝ // 0<s ∧ s<δ})(j N p:ℕ)(deep:j<N):Prop:=
      ∃ (V:(a:Fin (D+1))→Sight C a.val p)(u:(a:Fin (D+1))→Emblems C a.val)
        (est:∀a:Fin (D+1),Opened C a.val j p),
      (∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) j N p a.val
        (digits R N p 0) (V a) (u a)) ∧
      ∀(J:Type) [Fintype J] [DecidableEq J] (select:J→I),
      let deg:=d∘select
      let rad:=ρ∘select
      ∀ (branch:J→Bool)(v:(i:J)→S.Field (deg i).val) (c:J→Site ((C).side j p))(names:Census J),
      (∀i k:J,i≠k→((P).budget j).B^2<separation (c i) (c k)) →
      let L:=fun i=>(books (rad i)).rows (deg i)
      let x:=fun i=>((L i).arm (branch i) (v i)).source (N,p)
      let y:=fun i=>offer R (x i) (est (deg i)) deep.le
      let data:=fun i=>reduce (y i)
      let b:=fun i=>((C).S.toDepth deep.le p).embed (c i)
      (∀i,WilsonThermometerMarchSource.charge (y i) ≤ max 1
        (2*(β j)^(WilsonAddressedMixedStationRange.width T h*((deg i).val+1))*fee F (L i) (branch i) (v i))) ∧
      (∀turn:J→Motion,
        WilsonThermometerReflectedRoster.filed R (fun i=>(deg i).val) (fun _=>0) turn c data
          (fun i=>V (deg i)) (fun i=>u (deg i)) names deep.le t ∧
        ∀e (hj:e ≤ N)(s:names.Mode) U,
          (WilsonThermometerReflectedRoster.density R (fun i=>(deg i).val) (fun _=>0) turn c data
            (fun i=>u (deg i)) names deep.le hj U).part s =
          ((C).path.rep N p e).eval U • actualTransport C (N:=N)
            (fun W=>∏i∈s.val, ((WilsonThermometerMarchSource.charge (y i):ℝ):ℂ)⁻¹*
              (C).O N p (WilsonReflectedPublicOrientedFaces.displayed R (deg i).val (x i) (turn i)) (b i) W) hj U) ∧
      Income R (fun i=>(deg i).val) (fun _=>0) c data (fun i=>V (deg i)) (fun i=>u (deg i))
        names deep t (fun i W=>((WilsonThermometerMarchSource.charge (y i):ℝ):ℂ)⁻¹*(C).O N p (x i) (b i) W)

def Delivery (D T h t:ℕ)(d:I→Fin (D+1))(e:I→ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (M:I→ℝ)(ceiling:ℝ)(power target:ℕ)(ρ:I→{s:ℝ // 0<s ∧ s<δ})(f K:ℕ):Prop:=
    ∃up:f<K,∀N p(live:K≤N),
    let L:=fun i=>(books (ρ i)).rows (d i)
    let j:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
    ∃(first:∀i b,j i b≤f)(axes:(i:I)→Bool→Bool→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val),
      (∀i (mode b:Bool),Fixed R (d i).val (j i b) target N p f K (e i) (first i b) up.le live
        (((L i).arm b (field i (ρ i) mode b)).source (N,p)) (M i) (ceiling*(β K)^power) (axes i mode b)) ∧
      Gallery F D T h t d books ρ f N p (up.trans_le live)

def Course (D T h t:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)(M:I→ℝ)(E:I→ℕ)
    (e:I→ℕ)(pwr target:ℕ):Prop:=
    let τ:=depth ((2*pwr+∑i,E i)+1) (width T h) D
    let cap:=max 1 (4*∑i,M i)
    let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h τ D
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      let K:=berth R τ f
      (∀i (mode b:Bool),WilsonReflectedPublicStationFare.fee F ((books (ρ i)).rows (d i)) b (field i (ρ i) mode b)≤M i*(β f)^(E i)) →
      Delivery F D T h t d e books field M cap power target ρ f K

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1≤((P).budget i).supportExponent)
    (caps:∀i,((P).budget i).supportExponent≤100)(quote:OPE.Therm.Poetry (P))(D:ℕ):
    ∃t≥D+3,∀(T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)(M:I→ℝ)(E:I→ℕ)
    (_one:∀i,1≤M i)(e:I→ℕ)(pwr target:ℕ)(_reserve:∀i,e i+1≤2*pwr),
    Course F D T h t d books field M E e pwr target:=by
  classical
  obtain ⟨t,grade,press⟩:=WilsonSeparatedPrefixScreenedCampus.original (I:=I) F simple bliss slow shop D
  refine ⟨t,grade,?_⟩
  intro T h d δ books field M E one e pwr target reserve
  unfold Course
  intro τ cap power
  have all:=Filter.eventually_all.mpr fun k:Bool=>WilsonReflectedMixedLocatedSeats.original F simple bliss slow shop wide caps quote
    D T h d books (fun i s=>field i s k) M E one pwr target
  filter_upwards [all,press T h d books] with r received ballot
  intro ρ span near m f K salary
  have present(k:Bool):=received k ρ span near (fun i b=>salary i k b)
  let up:f<K:=(present false).choose
  refine ⟨up,?_⟩
  intro N p live L j
  have seat(i:I)(k b:Bool):=WilsonReflectedMixedMasterAxes.original R (d i).val (j i b) target N p f K (e i)
    up.le live (((L i).arm b (field i (ρ i) k b)).source (N,p)) (M i) (cap*(β K)^power)
    ((present k).choose_spec N p live i b (e i) (reserve i))
  choose first axes funded using seat
  exact ⟨fun i b=>first i false b,axes,funded,ballot ρ span near p N (up.trans_le live)⟩

end YM.Integration.WilsonReflectedMixedMasterRegistry
end
