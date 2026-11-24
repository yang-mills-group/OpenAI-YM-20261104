import YM.Integration.WilsonAddressedMixedStationRange
import YM.Integration.WilsonAddressedPublicGuardClock
import YM.Integration.WilsonMovingForkReporterClock
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedMixedThermalClock
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


omit [DecidableEq I] in
/-- At the genuine optical upper date the inverse original Wilson coupling
    pays one fixed power per restored basis grade throughout the moving window. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h t:ℕ)(d:I → Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z D T s.val):
    ∃A:ℝ,1 ≤ A ∧ ∀ᶠr in trail,∀ρ:I → {s:ℝ // 0<s ∧ s<δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) → 
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      (β (berth R t f))*(wilson z r)^2 ≤ A:=by
  classical
  let b:=2*T+11+2*h
  let c:=WilsonAddressedPublicGuardClock.ceiling G t 1
  have cp:0 ≤ c:=by
    have slope:0<G.slopeConstant:=Gauge.slopeConstant_pos simple
    change 0 ≤ 1+G.slopeConstant*((t:ℝ)+1)
    positivity
  obtain ⟨dollars,_,rate⟩:=WilsonMovingForkReporterClock.original F simple bliss b
  obtain ⟨gate,upper⟩:=eventually_atTop.mp (WilsonAddressedPublicGuardClock.thermal R simple slow t zero_lt_one)
  refine ⟨max 1 (c*dollars),le_max_left ..,?_⟩
  filter_upwards [rate,WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books,
    WilsonAddressedMixedStationRange.original F simple bliss slow D T h gate d books] with r checked spanOK range
  intro ρ span anchor m f
  have valid:=spanOK ρ span anchor
  obtain ⟨i,near⟩:=anchor
  have room:r ≤ (β f)^b*a f:=near▸(valid.2 i).2
  have step:=upper f (range ρ span ⟨i,near⟩).1
  have first:=checked f valid.1 room
  calc
    _ ≤ (c*(β f))*(wilson z r)^2:=mul_le_mul_of_nonneg_right step (sq_nonneg _)
    _=c*((β f)*(wilson z r)^2):=mul_assoc .. 
    _ ≤ c*dollars:=mul_le_mul_of_nonneg_left first cp
    _ ≤ _:=le_max_right .. 

end YM.Integration.WilsonAddressedMixedThermalClock
end
