import YM.Integration.WilsonOriginalTwoFlatIRPoolQuadrature
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolJet
open scoped ContDiff
open Metric
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


/-- A uniform first derivative on the actual normalized original fields,
with the same fixed finite physical axes as the determining tests. -/
theorem original (simple:G.Simple)(lead:Leading F Jr)
    (paid:∀j:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) j)
    {n:ℕ}(d:Fin n→ℕ)(x:∀i,RG17.Free C (d i)){K:Set (Points n)}(kc:IsCompact K)(safe:K⊆conf n):
    ∃ε A:ℝ,0<ε ∧ 1≤A ∧ ∀ᶠr in trail,∀X∈K,∀y∈closedBall X ε,
      let M:=fun z:Points n=>S.classMoment S d (r • z) (fun i=>homogeneous F Jr Z r (d i) (x i))
      ‖M X‖≤A ∧ ‖M y-M X‖≤A*dist y X:=by
  obtain ⟨ε,ep,domain⟩:=kc.exists_cthickening_subset_open (conf_open n) safe
  let W:=cthickening ε K
  have wc:IsCompact W:=kc.cthickening
  let free:=fun y=>(Bel (C).book).classMoment (Bel (C).book) d y x
  have regular:ContDiffOn ℝ ∞ free (conf n):=
    (Bel (C).book).class_smooth (Bel (C).book) (Maxwell.table_smooth (C).labels) (fun i=>⟨d i,x i⟩)
  have smooth(y)(hy:y∈W):ContDiffAt ℝ ∞ free y:=regular.contDiffAt ((conf_open n).mem_nhds (domain hy))
  have cont:ContinuousOn (fderiv ℝ free) W:=fun y hy=>((smooth y hy).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨B,bound⟩:=(wc.image_of_continuousOn (regular.continuousOn.mono domain)).isBounded.exists_norm_le
  obtain ⟨D,diff⟩:=(wc.image_of_continuousOn cont).isBounded.exists_norm_le
  let A:=1+max (max B D) 0
  have capB:1+B≤A:=add_le_add le_rfl ((le_max_left B D).trans (le_max_left _ 0))
  have capD:1+D≤A:=add_le_add le_rfl ((le_max_right B D).trans (le_max_left _ 0))
  refine ⟨ε,A,ep,by dsimp [A];linarith only [le_max_right (max B D) (0:ℝ)],?_⟩
  filter_upwards [WilsonPositionHomogeneousLeading.jets F Jr Z lead paid simple d x 0 wc domain zero_lt_one,
    WilsonPositionHomogeneousLeading.jets F Jr Z lead paid simple d x 1 wc domain zero_lt_one,self_mem_nhdsWithin]
    with r report gradient (rp:0<r)
  intro X hit y near M
  have h(y)(hy:y∈closedBall X ε):y∈W:=mem_cthickening_of_dist_le y X ε K hit hy
  have ox:X∈W:=self_subset_cthickening K hit
  have value₀:=norm_le_norm_sub_add (iteratedFDeriv ℝ 0 M X) (iteratedFDeriv ℝ 0 free X)
  rw [norm_iteratedFDeriv_zero,norm_iteratedFDeriv_zero] at value₀
  constructor
  · exact value₀.trans ((add_le_add (report X ox) (bound _ ⟨X,ox,rfl⟩)).trans capB)
  · rw [dist_eq_norm]
    apply (convex_closedBall X ε).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=M) _ _ (mem_closedBall_self ep.le) near
    · intro z hz
      let vals(i:Fin n):S.Tag:=⟨d i,homogeneous F Jr Z r (d i) (x i)⟩
      apply ((S.class_smooth S F.room.kernel.smooth vals).contDiffAt ((conf_open n).mem_nhds
        (Work.A05.smul_conf rp (domain (h z hz))))).differentiableAt (by simp) |>.comp z
      exact (differentiableAt_id.const_smul r)
    · intro y hy
      have whole:=norm_le_norm_sub_add (iteratedFDeriv ℝ 1 M y) (iteratedFDeriv ℝ 1 free y)
      rw [norm_iteratedFDeriv_one,norm_iteratedFDeriv_one] at whole
      exact whole.trans ((add_le_add (gradient y (h _ hy)) (diff _ ⟨y,h _ hy,rfl⟩)).trans capD)

end YM.Integration.WilsonOriginalTwoFlatIRPoolJet
end
