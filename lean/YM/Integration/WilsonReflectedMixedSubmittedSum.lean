import YM.Integration.WilsonReflectedMixedTrialDates
import YM.Integration.WilsonReflectedMixedTrialSumCash
import YM.Integration.WilsonReflectedMixedCutoffField
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReflectedMixedSubmittedSum
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

/-- The actual finite cutoff sources of the paid basis fields give a
representative of their complex superposition on their original extraction. -/
def submitted {ι:Type}[Fintype ι](c:ι→ℂ)(x:ι→S.Field d)
    (rows:∀i,WilsonThermometerUnitFilingFourSquare.Arm C S (l:Filter _) d (x i)):
    WilsonThermometerUnitFilingFourSquare.Arm C S (l:Filter _) d (∑i,c i•x i) where
  source a:=∑i,c i•(rows i).source a
  label:=∑i,c i•(rows i).label
  approaches:=tendsto_finsetSum Finset.univ (fun i _=>(rows i).approaches.const_smul (c i))
  represents:=by simp only [map_sum,map_smul,(rows _).represents]

/-- In the numerator with the reflected source the original finite labels
themselves acquire the conjugate coefficients. -/
theorem reflected {ι:Type}[Fintype ι](c:ι→ℂ)(x:ι→S.Field d)
    (rows:∀i,WilsonThermometerUnitFilingFourSquare.Arm C S (l:Filter _) d (x i))
    (s:Signed)(z:ℕ×ℕ):
    (WilsonThermometerUnitFilingFourSquare.reflected F (submitted c x rows) s).source z=
      ∑i,star (c i)•(WilsonThermometerUnitFilingFourSquare.reflected F (rows i) s).source z:=by
  change (C).book.mirrorGroup d s (star (∑i,c i•(rows i).source z))=_
  simp only [star_sum,star_smul,map_sum,map_smul]
  rfl

/-- Both original cutoff presentations can now use the explicitly assembled
basis portfolio to represent the same homogeneous continuum slot. -/
def positioned {ι:Type}[Fintype ι](J:ℝ→tower S)(Z:WilsonPrescription G)(r:ℝ)
    (c:ι→ℂ)(x:ι→RG17.Free C d)
    (rows:Bool→∀i,WilsonThermometerUnitFilingFourSquare.Arm C S (l:Filter _) d
      (homogeneous F J Z r d (x i))) (b:Bool):
    WilsonThermometerUnitFilingFourSquare.Arm C S (l:Filter _) d (homogeneous F J Z r d (∑i,c i•x i)) where
  source:=(submitted c _ (rows b)).source
  label:=(submitted c _ (rows b)).label
  approaches:=(submitted c _ (rows b)).approaches
  represents:=by simpa only [map_sum,map_smul] using (submitted c _ (rows b)).represents

end YM.Integration.WilsonReflectedMixedSubmittedSum
end
