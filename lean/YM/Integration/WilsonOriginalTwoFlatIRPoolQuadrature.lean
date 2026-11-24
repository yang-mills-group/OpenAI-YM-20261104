import YM.Integration.WilsonOriginalTwoFlatIRPoolLimit
import YM.Integration.WilsonOriginalTwoFlatIRPoolHeldGross
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolQuadrature
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


open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ → tower S)(Z:WilsonPrescription G)

open WilsonPositionThermometerGradedSource
local notation "heads" => source (C) (Finset.univ:Finset (Fin 3))
local notation "SiteSet" => {s:Finset (Fin 3)//s.Nonempty}

open WilsonPositionThermometerCapStation (Group)
open WilsonOriginalTwoFlatRoseNominated (face)
open WilsonOriginalTwoFlatRosePhase (fields)

open WilsonOriginalTwoFlatRoseBook (group)
open WilsonThermometerAlignedCells (atOrigin)
open WilsonOriginalTwoFlatRoseNominated (face)

open WilsonOriginalTwoFlatRoseRelativePhase (nodes recenter translated)

open WilsonMovingForkOpticalBook (reporter)
open WilsonOriginalTwoFlatIRSocketHeardCell (row incumbent held)
open WilsonOriginalTwoFlatIRPoolOrigins (home)
open WilsonReceivedChronologicalFixedRoseVariation (cells)

open WilsonPositionThermometerConnected (value)
open WilsonReceivedChronologicalFixedRoseVariation (signed)


open WilsonOriginalTwoFlatIRPoolBook (Tested)
open WilsonPositionThermometerConnected (value)
open WilsonOriginalObservedRoseMeshHeight (height)
open WilsonOriginalObservedRoseVanePurse (ages)
local notation "Faces" => Finset (Fin 3)


open WilsonOriginalTwoFlatIRPoolBook (direct)
open WilsonOriginalTwoFlatRoseFaceLimits (result)
open WilsonOriginalTwoFlatIRPoolRound (rounded)
open WilsonReceivedChronologicalFixedRoseVariation (signed)

/-- The authentic Wilson cutoff sample on the elected f-grid. -/
def microscopic {T:ℕ}{δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3)(r:ℝ)
    (ρ:Fin 3→{s:ℝ //0<s ∧ s<δ})(p:ℕ×ℕ):ℂ:=
  let f:=reporter F books ρ
  signed R φ r (f,p.2) (fun o=>value (incumbent R (N:=p.1)
    (fun i=>(home F Jr Z (books (ρ i)) (grade i) (x i)).arm.source p) (fun _=>direct) o.val))

/-- Its public continuum quadrature, before any interpolation in physical space. -/
def physical {T:ℕ}{δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3)(r:ℝ)
    (ρ:Fin 3→{s:ℝ //0<s ∧ s<δ}):ℂ:=
  let f:=reporter F books ρ
  let fields(i:Fin 3):=homogeneous F Jr Z (ρ i).val (grade i).val (x i)
  ∫y,φ y*value (result R r fields (rounded R r f y))

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (hl:(l:Filter _)≤order.fuse){T:ℕ}{δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3)(h:ℕ):
    ∀ᶠr in trail,∀ρ:Fin 3→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    Tendsto (microscopic F Jr Z books x φ r ρ) (l:Filter _) (𝓝 (physical F Jr Z books x φ r ρ)):=by
  obtain ⟨τ,positive,confined⟩:=φ.hasCompactSupport.exists_cthickening_subset_open (conf_open _) φ.tsupport_subset
  have clk:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have fee:(0:ℝ)^2<τ/12:=by simpa using div_pos positive (by norm_num:(0:ℝ)<12)
  filter_upwards [WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow 6 T h grade books,
    ((clk.conforms simple).pow 2).eventually (ge_mem_nhds fee),self_mem_nhdsWithin] with r mesh thin (rp:0<r)
  intro ρ span near
  let f:=reporter F books ρ
  have aperture:(C).S.a f≤(τ/12)*r:=(div_le_iff₀ rp).mp ((mesh ρ span near).1.trans thin)
  have small:4*(3:ℝ)*(C).S.a f≤τ*r:=by linarith
  exact WilsonOriginalTwoFlatIRPoolLimit.original R F (fun i=>homogeneous F Jr Z (ρ i).val (grade i).val (x i))
    (fun i=>(home F Jr Z (books (ρ i)) (grade i) (x i)).arm) simple hl r rp φ confined f small

end YM.Integration.WilsonOriginalTwoFlatIRPoolQuadrature
end
