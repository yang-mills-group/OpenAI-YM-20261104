import YM.Integration.WilsonReceivedChronologicalRosterBookedMesh
import YM.Integration.WilsonIndependentCapturedPages

/-! Original public geometry and the duration of its previously selected stop. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterBookedStop
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

open WilsonMovingForkOpticalBook (reporter)
open WilsonReceivedChronologicalFixedCellFee (factor capture)
open Next.Rank.Station

open WilsonPositionProgramReporterBand (Band)
open Pert.Asymptotics

omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h:ℕ)(d:I → Fin (D+1)){δ:ℝ}(books:(s:{s:ℝ // 0 < s ∧ s < δ}) → Book F (l:=l) H z D T s.val)
    {arity:ℕ}(φ:Test arity)(floor:ℕ){world:XSpace.Run}{stage u depth:ℕ}(band:Band R world stage)
    (v:WilsonIndependentCapturedPages.Stop R world band u depth)(active:0 < stage):
    ∀ᶠr in trail,∀ρ:I → {s:ℝ // 0 < s ∧ s < δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) → 
      let f:=reporter F books ρ
      let c:=capture R φ r
      ∀w:ℕ,c=band.reporter+w → floor ≤ c ∧ c+2 ≤ f ∧ 0 < v.date w ∧ v.date w ≤ c ∧
        a c/a f ≤ (β f)^(2*T+13+2*h) ∧
        R.family.S.scale c-R.family.S.scale (v.date w) ≤ 4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family c 0 c)⁻¹:=by
  obtain ⟨first,heard⟩:=eventually_atTop.mp v.heard
  filter_upwards [WilsonReceivedChronologicalRosterBookedMesh.original F simple bliss slow D T h d books φ,
    (WilsonAddressedPublicFirstRoseMovingDate.cofinal R φ).eventually_ge_atTop (max floor (band.reporter+first))]
    with r budget aged
  intro ρ radius nearest f c w centered
  change max floor (band.reporter+first) ≤ c at aged
  have after:floor ≤ c:=(le_max_left _ _).trans aged
  have later:band.reporter+first ≤ c:=(le_max_right _ _).trans aged
  have current:first ≤ w:=by omega
  have mesh:=budget ρ radius nearest
  refine ⟨after,mesh.1,active.trans_le ((band.ready w).trans (v.lower w)),(v.upper w).trans_eq centered.symm,mesh.2,?_⟩
  simpa only [centered] using ((heard w current).2 (band.reporter+w) 0 le_rfl).2.2.2

end YM.Integration.WilsonReceivedChronologicalRosterBookedStop
