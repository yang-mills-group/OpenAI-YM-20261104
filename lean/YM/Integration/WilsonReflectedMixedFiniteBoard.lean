import YM.Integration.WilsonReflectedMixedSubmittedHearing
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReflectedMixedFiniteBoard
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


open WilsonThermometerUnitFilingFourSquare
open WilsonPositionHomogeneousFrame
open MS MS.Land FVA2 FVA2.Register

variable {d:ℕ}



open WilsonReflectedMixedSubmittedHearing (placed)

def scalar (m:Option Signed)(z:ℂ):ℂ:=match m with
  | none=>z
  | some _=>star z

theorem column {ι:Type}[Fintype ι](m:Option Signed)(c:ι→ℂ)(v:ι→(C).label d):
    placed (R:=R) m (∑i,c i•v i)=∑i,scalar m (c i)•placed (R:=R) m (v i):=by
  cases m with
  | none=>rfl
  | some s=>simp only [WilsonReflectedMixedSubmittedHearing.placed,scalar,star_sum,star_smul,map_sum,map_smul]

/-- The native finite Wilson expectation of all original source labels at
their real separately translated lattice sites. -/
theorem numeric {n:ℕ}(N p:ℕ)(d k:Fin n→ℕ)(m:Fin n→Option Signed)
    (c:(i:Fin n)→Fin (k i)→ℂ)(Y:(i:Fin n)→Fin (k i)→(C).label (d i))(o:Fin n→Site ((C).side N p)):
    (C).numeric N p (fun i=>⟨d i,placed (R:=R) (m i) (∑a,c i a•Y i a)⟩) o=
      ∑s:(i:Fin n)→Fin (k i),(∏i,scalar (m i) (c i (s i)))*
        (C).numeric N p (fun i=>⟨d i,placed (R:=R) (m i) (Y i (s i))⟩) o:=by
  change (C).ensemble (N:=N) (p:=p) d o (fun i=>placed (R:=R) (m i) (∑a,c i a•Y i a))=_
  simp_rw [column]
  simp only [MultilinearMap.map_sum,MultilinearMap.map_smul_univ,smul_eq_mul]
  rfl

/-- This is the original physical finite test sum with its own mesh prefactor,
before either regulator. -/
theorem original {n:ℕ}(N p:ℕ)(d k:Fin n→ℕ)(m:Fin n→Option Signed)
    (c:(i:Fin n)→Fin (k i)→ℂ)(Y:(i:Fin n)→Fin (k i)→(C).label (d i))(t:Test n):
    Order.smears C N p (fun i=>⟨d i,placed (R:=R) (m i) (∑a,c i a•Y i a)⟩) t=
      ∑s:(i:Fin n)→Fin (k i),(∏i,scalar (m i) (c i (s i)))*
        Order.smears C N p (fun i=>⟨d i,placed (R:=R) (m i) (Y i (s i))⟩) t:=by
  simp only [Order.smears,numeric N p d k m c Y]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro o _
  ring

end YM.Integration.WilsonReflectedMixedFiniteBoard
end
