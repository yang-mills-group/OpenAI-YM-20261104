import YM.Integration.WilsonSeparatedPrefixMovingHomeEars

/-! The full selected ordinary face at the detector stencil is the original cutoff word with the same fine anchors. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixScreenedWord
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

open WilsonThermometerReflectedTrajectory WilsonOriginalTwoFlatGridCapture
variable {G:Gauge}(R:Run G){E:Type}[Fintype E][DecidableEq E]{f N p:ℕ}
local notation "C" => R.family

theorem original (d:E→ℕ)(deep:f≤N)(site:E → Cover)(v:∀i,(C).label (d i)):
    (fun U=>∏i∈(Stock.final E).val,(C).O N p
      (WilsonReflectedPublicOrientedFaces.displayed R (d i) (v i) (1,false))
      (anchorAt R (snap (C) f p site i) N) U)=word R d f N p deep site v:=by
  have idle(i):WilsonReflectedPublicOrientedFaces.displayed R (d i) (v i) (1,false)=v i:=by
    simp [WilsonReflectedPublicOrientedFaces.displayed,show (1:Signed).ortho=1 from map_one Signed.inclusionO]
  funext U
  change (∏i,(C).O N p _ (anchorAt R (snap (C) f p site i) N) U)=_
  simp only [idle,WilsonAddressedPublicGridRooms.top R deep,word]

omit [DecidableEq E] in
theorem funded (d:E→ℕ)(deep:f≤N)(site:E → Cover)(v:∀i,(C).label (d i)):
    Continuous (word R d f N p deep site v):=continuous_finsetProd _ fun _ _=>(C).continuousO _ _ _ _ _

end YM.Integration.WilsonSeparatedPrefixScreenedWord
end
