import YM.Integration.WilsonMeasuredPublicEntranceProfileWindow
import YM.Integration.WilsonMeasuredPublicEntranceProfileSites
/-! The actual public reporting mesh resolves each fixed separated test uniformly before the cutoff and period. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceProfileMesh
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


omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(D T n:ℕ){δ:ℝ}
    (book:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val){t:ℝ}(tp:0<t):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ //0<s ∧ s<δ},(∃i,(ρ i).val=r) →
    let m:=univ.sup fun i=>max (book (ρ i)).stock.j (book (ρ i)).W.k
    4*(n:ℝ)*(C).S.a (berth R 5 m)≤t*r:=by
  classical
  obtain ⟨gate,pay⟩:=eventually_atTop.mp ((hat_rate (P) simple).eventually_ge_atTop (4*(n:ℝ)/t))
  filter_upwards [(ge_mem_nhds ((C).S.a_pos gate)).filter_mono nhdsWithin_le_nhds] with r past
  intro ρ near m
  obtain ⟨i,anchor⟩:=near
  have fine:(book (ρ i)).W.k ≤ m:=(le_max_right ..).trans
    (Finset.le_sup (f:=fun k:I=>max (book (ρ k)).stock.j (book (ρ k)).W.k) (mem_univ i))
  have tight:(C).S.a m≤r:=((C).S.strictAnti.antitone fine).trans
    (((WilsonReflectedPublicBulbBerth.mesh R _ (book (ρ i)).checked).trans (book (ρ i)).active.le).trans anchor.le)
  have high:gate ≤ m:=by
    by_contra! early
    exact (not_lt_of_ge (tight.trans past)) ((C).S.strictAnti early)
  have funding:4*(n:ℝ)≤(β m)*t:=(div_le_iff₀ tp).mp (pay m high)
  have power:β m≤(β m)^5:=by
    calc
      _=(β m)^1:=(pow_one _).symm
      _≤_:=pow_le_pow_right₀ ((P).fits.delayed m).le (by norm_num)
  calc
    _≤((β m)*t)*(C).S.a (berth R 5 m):=mul_le_mul_of_nonneg_right funding ((C).S.a_pos _).le
    _=t*((C).S.a (berth R 5 m)*(β m)):=by ring
    _≤t*((C).S.a (berth R 5 m)*(β m)^5):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left power ((C).S.a_pos _).le) tp.le
    _≤_:=mul_le_mul_of_nonneg_left ((WilsonInvariantActionPosition.arrival R 5 m).2.trans tight) tp.le

end YM.Integration.WilsonMeasuredPublicEntranceProfileMesh
end
