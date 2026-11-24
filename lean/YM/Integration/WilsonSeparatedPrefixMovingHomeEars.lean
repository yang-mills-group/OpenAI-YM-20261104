import YM.Integration.WilsonSeparatedPrefixHomeCharge
import YM.Integration.WilsonSeparatedPrefixCanonicalFlatRaw
import YM.Integration.WilsonAddressedMixedStationEstate
import YM.Integration.WilsonSeparatedPrefixCanonicalClearRaw
import YM.Integration.WilsonSeparatedPrefixCanonicalClock

/-! Hear the original finite roster at separately nominated public radii on its actual shared separated board. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingHomeEars
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
open MS MS.Land FVA2 FVA2.Register


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

open WilsonThermometerUnitFilingCoarse WilsonSeparatedPrefixCanonicalClearConvolution
open Lodestar
local notation "J₀" => Marks I
local notation "X" => Unit×(I×Bool)


def returned {N p f b:ℕ}(live:f≤N)(bf:b≤f)(source:Config G ((C).side N p)→ℂ)
    (regular:Config G ((C).side f p)→ℂ)(W:Config G ((C).side b p))(amount:ℝ):Prop:=
  Integrable (fun U=>(((C).path.rep N p f).eval U:ℂ)*regular U) (prior G _) ∧
  ‖actualTransport (C) (N:=N) (fun U=>actualTransport (C) (N:=N) source live U-regular U) bf W‖≤amount

theorem original (Jr:ℝ→tower S)(Z₀:WilsonPrescription G)
    (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(quoted:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(D T h:ℕ)(d:I→Fin (D+1))
    (name:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (slip:∀s,WilsonMovingForkWindowBooks.Priced F (books s))
    (cater:Cater (C) R.doors)(bank:WilsonThermometerClusterProjectionBudget.Ready (P))
    (wage:WilsonReportLampForecast.Ready (P))(nested:WilsonPositionProgramNestedLengths.Nested R.rolls)
    (window room target:ℕ):
    ∃M:ℝ,1≤M ∧ ∃t≥D+3,∃j₀:ℕ,∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      ∀p N(deep:f<N),∃(V:(a:Fin (D+1))→Sight C a.val p)(u:(a:Fin (D+1))→Emblems C a.val)
        (est:∀a:Fin (D+1),Opened C a.val f p),
      (∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p a.val
        (digits R N p 0) (V a) (u a)) ∧
      ∀(branch:I→Bool)(turn:I→Motion)(o:I→Site ((C).side f p))(j:ℕ)(_late:j₀≤j)(height:j≤f),
      let v:=fun i=>WilsonPositionHomogeneousFrame.homogeneous F Jr Z₀ (ρ i).val (d i).val (name i)
      let L:=fun i=>(books (ρ i)).rows (d i)
      let x:=fun i=>((L i).arm (branch i) (v i)).source (N,p)
      let y:=fun i=>offer R (x i) (est (d i)) deep.le
      let data:=fun i=>reduce (y i)
      let Q:=(C).path.rep N p f
      let b:=fun i=>anchorAt R (o i) N
      let Z:=fun i=>marked R (N:=N) 0 (turn i) (o i) (V (d i)) (u (d i)) (data i) f
      let route:=fun k (a:X)=>WilsonOriginalNullOriginGridRoster.ancestry R p f (o a.2.1) k
      let source:=fun (s:(J₀).Mode) W=>∏i∈s.val,(C).O N p (displayed R (d i).val (x i) (turn i)) (b i) W
      let regular:=fun (s:(J₀).Mode) U=>∏i∈s.val,((WilsonThermometerMarchSource.charge (y i):ℝ):ℂ)*(Z i).2.1 U
      (C).S.a j/(C).S.a f≤(β f)^window → ((P).params f).supportExponent=100 → 5≤Q.p.B →
      (∀i k:I,i≠k→Q.p.B^2+1 ≤ separation (o i) (o k)) →
      WilsonThermometerReflectedRoster.filed R (fun i=>(d i).val) (fun _=>0) turn o data
        (fun i=>V (d i)) (fun i=>u (d i)) J₀ deep.le t ∧
      (2≤((P).budget j).supportExponent→∀W:Config G ((C).side j p),
        flags ((C).path.rep N p j).p.threshold W=∅ →∀s:(J₀).Mode,
        returned (R:=R) deep.le height (source s) (regular s) W (M*((β f)^target)⁻¹)) ∧
      (∀(_finer:j+2≤f)(l₀:ℕ)(anchor:X),l₀≤room→
        (∀i,coverNumber ((C).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l₀) →
        ((P).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
        ∀e:ℕ,(C).ref 0≤e→∀ej:e≤j,Opened C 0 e p→Opened C 0 j p→∀s:(J₀).Mode,
        returned (R:=R) deep.le (ej.trans height) (source s) (regular s) 1 (M*((β f)^target)⁻¹)):=by
  classical
  obtain ⟨M,one,extra,prices⟩:=WilsonSeparatedPrefixHomeCharge.original F Jr Z₀ simple bliss slow lead quoted
    D T h d name books slip
  obtain ⟨t,degree,loans⟩:=WilsonAddressedMixedStationEstate.original F simple bliss slow shop D (I:=I)
  obtain ⟨jc,clears⟩:=eventually_atTop.mp (WilsonSeparatedPrefixCanonicalClearRaw.original R
    (fun i=>(d i).val) simple shop slow cater wage nested window (target+extra) t)
  obtain ⟨jf,flats⟩:=eventually_atTop.mp (WilsonSeparatedPrefixCanonicalFlatRaw.original R
    (fun i=>(d i).val) simple shop slow cater bank wage nested window room (target+extra) t)
  refine ⟨M,one,t,degree,max jc jf,?_⟩
  filter_upwards [loans T h d books,prices] with r earned payable ρ band hits m f p N deep
  obtain ⟨V,u,est,enrolled,sale⟩:=earned ρ band hits p N deep
  refine ⟨V,u,est,enrolled,?_⟩
  intro branch turn o j late height v L x y data Q b Z route source regular span fixed large apart
  have budget:Q.p=(P).budget f:=(R.makes.wilson.represents N p f deep.le).vac
  have separated (i k:I)(ne:i≠k):((P).budget f).B^2<separation (o i) (o k):=by
    rw [←budget];exact Nat.lt_of_succ_le (apart i k ne)
  obtain ⟨money,issued,_⟩:=sale branch v o J₀ separated
  have filed:=(issued turn).1
  have bill:=payable ρ band hits branch (fun i=>WilsonThermometerMarchSource.charge (y i))
    (fun i=>(WilsonThermometerMarchSource.charged (y i)).le) money
  have course:route f=(o∘Prod.fst) ∘ Prod.snd:=funext (fun a=>WilsonOriginalNullOriginGridRoster.starts R p f (o a.2.1))
  have parent(k)(hk:k<f):route k=((P).clock.op k p).ratio.parent ∘ route (k+1):=
    funext (fun a=>(WilsonOriginalNullOriginGridRoster.route R p f (o a.2.1) hk).symm)
  refine ⟨filed,?_,?_⟩
  · intro floor W clearW s
    obtain ⟨held,fee⟩:=clears j ((le_max_left jc jf).trans late) N p f height deep (fun i=>V (d i)) (fun i=>u (d i)) (fun i=>est (d i))
      (fun i=>enrolled (d i)) x turn o route filed span fixed large apart course (fun k _=>parent k) floor W clearW s
    exact ⟨held,fee.trans (bill s.val target)⟩
  · intro finer l₀ anchor housed housing zero e he ej oe oj s
    obtain ⟨held,fee⟩:=flats j ((le_max_right jc jf).trans late) N p f finer deep l₀ (fun i=>V (d i)) (fun i=>u (d i)) (fun i=>est (d i))
      (fun i=>enrolled (d i)) x turn o route anchor filed housed span fixed large apart course (fun k _=>parent k) housing zero e he ej oe oj s
    exact ⟨held,fee.trans (bill s.val target)⟩

end YM.Integration.WilsonSeparatedPrefixMovingHomeEars
end
