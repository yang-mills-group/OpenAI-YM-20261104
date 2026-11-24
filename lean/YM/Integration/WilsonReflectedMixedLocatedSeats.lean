import YM.Integration.WilsonReflectedMixedThermalElection
import YM.Integration.WilsonReflectedMixedFundedSeat
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonReflectedMixedLocatedSeats
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
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open WilsonOriginalTwoFlatPublicNamedFare (chosen)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)



open WilsonAddressedMixedStationRange (width)
open WilsonMeasuredPublicEntranceGridDebit (fitted bill settled)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedPublicSignedFare (amplitude)
open WilsonAddressedPublicGuardFare (word)
open OPE.Therm (Poetry)



open WilsonReflectedMixedFundedSeat

omit [DecidableEq I] in
/-- Full master berth for each independently chosen public arm.  The requested
roster's repeated appearances of a master slot can take different branches. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1≤((P).budget i).supportExponent)
    (caps:∀i,((P).budget i).supportExponent≤100)(quote:Poetry (P))
    (D T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val)
    (M:I→ℝ)(E:I→ℕ)(one:∀i,1≤M i)(pwr target:ℕ):
    let t:=depth ((2*pwr+∑i,E i)+1) (width T h) D
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      let K:=berth R t f
      let L:=fun i=>(books (ρ i)).rows (d i)
      (∀i b,WilsonReflectedPublicStationFare.fee F (L i) b (field i (ρ i) b)≤M i*(β f)^(E i)) →
      ∃up:f<K,∀N p (live:K≤N) i b (e:ℕ),e+1≤2*pwr →
        Seat R (d i).val (WilsonReflectedPublicStationFare.station F (L i) b) target N p f K e up.le live
          (((L i).arm b (field i (ρ i) b)).source (N,p)) (M i)
          (max 1 (4*∑i,M i)*(β K)^((∑i,E i)+WilsonAddressedMixedRawTrial.power T h t D)):=by
  classical
  intro t
  filter_upwards [WilsonReflectedMixedThermalElection.original F simple bliss slow shop wide quote D T h d books
    M E one pwr target] with r opening
  intro ρ span near m f K L salary
  obtain ⟨up,offer⟩:=opening ρ span near
  refine ⟨up,?_⟩
  intro N p live i b e bound
  let branch: I→Bool:=fun _=>b
  let v:=fun k=>field k (ρ k) (branch k)
  let source:=fun k=>((L k).arm (branch k) (v k)).source (N,p)
  let j:=fun k=>WilsonReflectedPublicStationFare.station F (L k) (branch k)
  have funded:=offer branch v (fun k=>salary k (branch k)) N p live
  exact WilsonReflectedMixedFundedSeat.original R (fun k=>(d k).val) j (fun _=>e) up live source M
    (fun k=>zero_le_one.trans (one k)) (fun _=>bound) (caps f) funded i

end YM.Integration.WilsonReflectedMixedLocatedSeats
end
