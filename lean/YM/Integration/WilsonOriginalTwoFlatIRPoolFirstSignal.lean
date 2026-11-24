import YM.Integration.WilsonOriginalTwoFlatIRPoolFirstGrid
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolFirstSignal
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



open WilsonOriginalTwoFlatRoseFaceLimits (names loc)
open Metric
local notation "faces" => Finset (Fin 3)


open WilsonMaxwellThermometerNominatedSecant (bill budget)
open WilsonOriginalTwoFlatIRPoolQuadrature (physical)

/-- The public integrated value on its actual continuum positions. -/
def smooth (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3)(r:ℝ):ℂ:=
  let v:=fun i=>homogeneous F Jr Z r (grade i).val (x i)
  ∫y,φ y*value (result R r v y)

private theorem secant (S T:faces→ℂ){B A:ℝ}(gross:1≤B)(ap:0≤A)
    (left:∀s,‖S s‖≤B)(right:∀s,‖T s‖≤B+1)(each:∀s,‖S s-T s‖≤A):
    ‖value S-value T‖≤7*((B+1)+2*(B+1)^2)*A:=by
  rw [WilsonMaxwellThermometerNominatedSecant.signed]
  apply (norm_sum_le ..).trans
  calc _≤∑s:faces,‖bill S T s‖*A:=sum_le_sum fun s _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (each s) (norm_nonneg _)
       _=(∑s:faces,‖bill S T s‖)*A:=(sum_mul ..).symm
       _≤_:=by
         have bought:=budget S T B (B+1) (fun s _ _=>left s) (fun i=>right {i})
         rw [max_eq_right (show B≤B+1 by linarith),max_eq_right (show 1≤B+1 by linarith)] at bought
         exact mul_le_mul_of_nonneg_right bought ap

/-- The true mesh already recovers the first public coupling response at equal
home radii. The error is quadratic in the original public coupling. -/
theorem grid (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F Jr)
    (paid:∀j:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) j)
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3):
    ∃C₀:ℝ,0≤C₀ ∧ ∀ᶠr in trail,∀f:ℕ,(C).S.a f/r≤(wilson z r)^2→
    let v:=fun i=>homogeneous F Jr Z r (grade i).val (x i)
    ‖smooth F Jr Z x φ r-(∫y,φ y*value (result R r v (rounded R r f y)))‖≤
      (∫y,‖φ y‖)*C₀*(wilson z r)^2:=by
  choose B A bp ap sale using fun s:faces=>WilsonOriginalTwoFlatIRPoolFirstGrid.faces_at F Jr Z simple bliss lead paid x φ s
  let T:=1+∑s,B s
  let cost:=∑s,A s
  have tp:1≤T:=by dsimp [T];linarith only [sum_nonneg (s:=univ) (fun (s:faces) _=>zero_le_one.trans (bp s))]
  have cp:0≤cost:=sum_nonneg fun s _=>ap s
  have eachB(s:faces):B s≤T:=by
    have e:=single_le_sum (f:=B) (fun j _=>zero_le_one.trans (bp j)) (mem_univ s)
    dsimp [T];linarith only [e]
  have eachA(s:faces):A s≤cost:=single_le_sum (f:=A) (fun j _=>ap j) (mem_univ s)
  let unit:=7*((T+1)+2*(T+1)^2)
  have up:0≤unit:=by dsimp [unit];positivity
  have con:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have limit:Tendsto (fun r=>cost*(wilson z r)^2) trail (𝓝 0):=by
    simpa using (tendsto_const_nhds (x:=cost)).mul ((con.conforms simple).pow 2)
  refine ⟨unit*cost,mul_nonneg up cp,?_⟩
  filter_upwards [Filter.eventually_all.mpr sale,limit.eventually (ge_mem_nhds zero_lt_one),self_mem_nhdsWithin]
    with r available small (rp:0<r)
  intro f fine v
  let S₀:Points 3→faces→ℂ:=result R r v
  let S₁:=fun y:Points 3=>S₀ (rounded R r f y)
  let e:=cost*(wilson z r)^2
  have estimate(y)(hit:y∈tsupport (φ:Points 3→ℂ)):
      ‖value (S₀ y)-value (S₁ y)‖≤unit*e:=by
    have labs(s:faces):=available s f fine y hit
    have orig(s:faces):‖S₀ y s‖≤T:=(labs s).1.trans (eachB s)
    have diff(s:faces):‖S₁ y s-S₀ y s‖≤e:=(labs s).2.trans (mul_le_mul_of_nonneg_right (eachA s) (sq_nonneg _))
    apply secant _ _ tp (mul_nonneg cp (sq_nonneg _)) orig
    · intro s
      exact (norm_le_norm_sub_add _ (S₀ y s)).trans ((add_le_add (diff s) (orig s)).trans (by dsimp [e];linarith only [small]))
    · intro s; rw [norm_sub_rev];exact diff s
  have tested:Integrable (fun y:Points 3=>φ y*value (S₀ y)) volume:=
    φ.smearing (WilsonPositionThermometerConnected.continuous_value.comp_continuousOn
      (WilsonOriginalTwoFlatRosePhysical.continuum R F v rp))
  have measurable:Measurable (fun y=>value (S₁ y)):=WilsonOriginalTwoFlatIRPoolRound.field R r f (fun y=>value (S₀ y))
  have signed (y:Points 3):‖φ y*value (S₀ y)-φ y*value (S₁ y)‖≤‖φ y‖*(unit*e):=by
    by_cases none:φ y=0
    · simp [none]
    · rw [←mul_sub,norm_mul];exact mul_le_mul_of_nonneg_left (estimate y (subset_tsupport _ none)) (norm_nonneg _)
  have φi:Integrable (fun y:Points 3=>φ y) volume:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have error:= (φi.norm.mul_const (unit*e)).mono' (tested.aestronglyMeasurable.sub
    (φ.continuous.measurable.mul measurable).aestronglyMeasurable) (Eventually.of_forall signed)
  have other:Integrable (fun y:Points 3=>φ y*value (S₁ y)) volume:=(tested.sub error).congr
    (Eventually.of_forall fun _=>sub_sub_cancel ..)
  change ‖(∫y,φ y*value (S₀ y))-(∫y,φ y*value (S₁ y))‖≤_
  calc _≤(∫y,‖φ y‖)*(unit*e):=by
         rw [←integral_sub tested other,←integral_mul_const]
         exact norm_integral_le_of_norm_le (φi.norm.mul_const _) (Eventually.of_forall signed)
       _=_:=by dsimp [e];ring

end YM.Integration.WilsonOriginalTwoFlatIRPoolFirstSignal
end
