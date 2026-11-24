import YM.Integration.WilsonSeparatedPrefixGridGround
import YM.Integration.WilsonOriginalTwoFlatIRPoolChamber
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolSites
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

open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonReceivedChronologicalFixedRoseVariation (cells)

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {T:ℕ}{δ:ℝ}(books:(s:{s:ℝ //0 < s ∧ s < δ})→Book F (l:=l) H z 6 T s.val)(φ:Test 3)(h:ℕ):
    ∃apron:ℕ,∀floor:ℕ,∀ᶠr in trail,∀ρ:Fin 3→{s:ℝ//0<s ∧ s<δ},
    (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) → (∃i,(ρ i).val=r) →
    let f:=reporter F books ρ
    ∃j:ℕ,floor≤j ∧ j+2≤f ∧ ∀N per,f≤N → ∀o:cells R φ r (f,per),
      Ground R N per j f apron o.val ∧
      ∀i k:Fin 3,i≠k → ((P).budget f).B^2<separation (o.val i) (o.val k):=by
  classical
  obtain ⟨M,mp,η,ep,housed⟩:=WilsonCenteredReaderDomain.room φ
  have shape:∀x:Points 3,φ x≠0 →
      (∀i,‖x i‖≤M) ∧ Pairwise fun i k=>η≤‖x i-x k‖:=by
    intro x active
    have receipt:=housed 1 zero_lt_one x (subset_closure active)
    exact ⟨fun i=>by simpa using receipt.span i,fun i k ne=>by simpa using receipt.spaced i k ne⟩
  obtain ⟨apron,ground⟩:=WilsonSeparatedPrefixGridGround.original F simple bliss slow 6 T h grade books
    (L:=M+1) (η:=η/2) (by linarith) (half_pos ep)
  refine ⟨apron,?_⟩
  intro floor
  have clk:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have thresh:(0:ℝ)^2 < min 1 (η/4)/12:=by
    rw [zero_pow (by decide:2≠0)]
    exact div_pos (lt_min zero_lt_one (by positivity)) (by norm_num)
  have mesh:=WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow 6 T h grade books
  filter_upwards [ground floor,self_mem_nhdsWithin,clk.positive,(clk.conforms simple).eventually (ge_mem_nhds zero_lt_one),
    ((clk.conforms simple).pow 2).eventually (ge_mem_nhds thresh),mesh] with r realGround rp gp small thin widths
  intro ρ span near f
  obtain ⟨j,gate,early,atSite⟩:=realGround ρ span near
  refine ⟨j,gate,early,?_⟩
  have rpos:0<r:=rp
  have grow:r≤outer z h r:=by obtain ⟨i,eq⟩:=near;exact eq ▸ (span i).2
  have debt:(C).S.a f ≤ min 1 (η/4)/12*r:=(div_le_iff₀ rpos).mp ((widths ρ span near).1.trans thin)
  have first:=mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) (η/4)) rpos.le
  have second:=mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (η/4)) rpos.le
  have small₁:4*(3:ℝ)*(C).S.a f≤r:=by linarith only [debt,first]
  have small₂:4*(3:ℝ)*(C).S.a f≤η/4*r:=by linarith only [debt,second]
  intro N per live o
  obtain ⟨site,registered,admitted⟩:=WilsonMeasuredPublicEntranceProfileSites.lifted R φ (per:=per) rpos shape small₁ small₂
  obtain ⟨inside,apart⟩:=admitted o.val (WilsonReceivedChronologicalFixedRoseVariation.charged R φ r (f,per) o)
  have entered:Ground R N per j f apron o.val:=by
    rw [←registered o.val]
    exact (atSite (Fin 3) N per live (site o.val)
      (fun i=>(inside i).trans (mul_le_mul_of_nonneg_left grow (by linarith))) apart).1
  refine ⟨entered,?_⟩
  intro i k ne
  have own:=entered.2.1 i k ne
  have equal:((C).path.rep N per f).p=(P).budget f:=(R.makes.wilson.represents N per f live).vac
  rw [equal] at own
  exact own

end YM.Integration.WilsonOriginalTwoFlatIRPoolSites
end
