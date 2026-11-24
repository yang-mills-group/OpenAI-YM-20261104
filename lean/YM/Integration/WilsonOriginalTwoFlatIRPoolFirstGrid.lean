import YM.Integration.WilsonOriginalTwoFlatIRPoolJet
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolFirstGrid
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

private theorem distance {n f:ℕ}{r:ℝ}(rp:0<r)(X:Points n):
    dist (rounded R r f X) X ≤ (4*(n:ℝ))*((C).S.a f/r):=by
  have located:r • rounded R r f X=tag ((C).S.a f) (address ((C).S.a f) (r • X)):=by simp [rounded,smul_smul,rp.ne']
  have dist₀:dist (r • rounded R r f X) (r • X)=r*dist (rounded R r f X) X:=by
    rw [dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos rp,dist_eq_norm]
  rw [←mul_div_assoc]
  apply (le_div_iff₀ rp).2
  rw [mul_comm,←dist₀,located]
  exact Extraction.approximate ((C).S.a_pos f) (r • X)

/-- Each of the genuine seven faces has a bounded first jet on the prescribed
compact separated profile. Degree zero is included for the connected test. -/
theorem faces_at (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F Jr)
    (paid:∀j:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) j)
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3)(s:faces):
    ∃B A:ℝ,1≤B ∧ 0≤A ∧ ∀ᶠr in trail,∀f:ℕ,(C).S.a f/r≤(wilson z r)^2→
    ∀X∈tsupport φ,let v:=fun i=>homogeneous F Jr Z r (grade i).val (x i)
    ‖result R r v X s‖≤B ∧ ‖result R r v (rounded R r f X) s-result R r v X s‖≤A*(wilson z r)^2:=by
  let n:=Fintype.card ↥s
  let d(i:Fin n):=(grade (names s i).val).val
  let head(i:Fin n):=(x (names s i).val)
  let K:=loc s '' tsupport (φ:Points 3→ℂ)
  have kc:IsCompact K:=φ.hasCompactSupport.image (WilsonOriginalTwoFlatRoseFaceLimits.continuous_loc s)
  have clear:K⊆conf n:=by
    rintro _ ⟨x,hx,rfl⟩
    exact WilsonOriginalTwoFlatRoseFaceLimits.separate s (φ.tsupport_subset hx)
  obtain ⟨ε,B,ep,bp,sale⟩:=WilsonOriginalTwoFlatIRPoolJet.original F Jr Z simple lead paid d head kc clear
  have bp₀:0≤B:=zero_le_one.trans bp
  let w:ℝ:=4*n
  have wp:0≤w:=by dsimp [w];positivity
  have weak:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have tiny:Tendsto (fun r=>w*(wilson z r)^2) trail (𝓝 0):=by
    simpa using (tendsto_const_nhds (x:=w)).mul ((weak.conforms simple).pow 2)
  refine ⟨B,B*w,bp,mul_nonneg bp₀ wp,?_⟩
  filter_upwards [sale,tiny.eventually (ge_mem_nhds ep),self_mem_nhdsWithin] with r received small (rp:0<r)
  intro f mesh X here v
  have identity:loc s (rounded R r f X)=rounded R r f (loc s X):=rfl
  have delta:dist (loc s (rounded R r f X)) (loc s X)≤w*(wilson z r)^2:=by
    rw [identity]
    exact (distance (R:=R) rp (loc s X)).trans (mul_le_mul_of_nonneg_left mesh wp)
  have invoice:=received (loc s X) ⟨X,here,rfl⟩ (loc s (rounded R r f X)) (delta.trans small)
  exact ⟨invoice.1,(invoice.2.trans (mul_le_mul_of_nonneg_left delta bp₀)).trans_eq (mul_assoc ..).symm⟩

end YM.Integration.WilsonOriginalTwoFlatIRPoolFirstGrid
end
