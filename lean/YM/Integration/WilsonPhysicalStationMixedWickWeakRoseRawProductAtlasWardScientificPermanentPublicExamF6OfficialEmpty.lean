import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6RawDressing
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialEmpty
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
variable {G : Gauge} {W : Type} [LinearOrder W]

theorem vacant (team : Team) (η : ℝ) (side : Side) (b : Bool) (place : W → Cover) (anchor : Cover)
    (V : W → Actor G) (row : ℕ → ℂ) (paid : PhysicalSum G team η side b (∅ : Finset W) place anchor V row) :
    row = Trunk.unit := by
  let p : Sector (FixedMode G side) := σbranch
  let marks := Marks V η side anchor place
  let Q := NRG (Stripped team) η side G b
  let master := Master G side b
  have blank : marks (∅ : Finset W) = 0 := by simp [marks,Marks]
  have letter : Font p marks (∅ : Finset W) = (PermV p).unit :=
    Stencil.simple_E (PermV p) marks (marked W) blank
  have reference : Endμ master p Q (Font p marks (∅ : Finset W)) Trunk.unit := by
    unfold Endμ
    rw [letter,(PermV p).identityR,Trunk.identityR]
  exact Swirl.classicalμ (Q := Q) (τ_nil (b := b) (Stripped team) η side G) paid reference

theorem heat (j : ℕ) : Trunk.unit j = if j=0 then 1 else 0 := by
  change useN.refineV (1 : ℂ) j = _
  unfold SplitP.refineV
  by_cases hj : j=useN.origin
  · rw [if_pos hj,if_pos (show j=0 from hj)]
  · rw [if_neg hj,if_neg (show j≠0 from hj)]

variable (Z : WilsonPrescription G) {simple : G.Simple} {σ : Prescription (Press.portDeck G)} {dial : Bool}
    (matched : Main.Match Z simple (WilsonCapturedPhysicalMSDatum.original G) σ dial)
include matched in
theorem original (m : XSpace.Mesh) (even : Even m.p.side.val) (place : W → Cover) (anchor : Cover)
    (η : ℝ) (letters : W → Label (Press.portDeck G)) :
    let row := Change.convertSources (Change.Dictionary.paid letters σ η) (∅ : Finset W).toList fun l =>
      Program.substitute (Program.shift σ.team η)
        (Slice.record (Birth.words Z.scheme m.p.side (l.map (Top.declares letters anchor place))))
    PhysicalSum G σ.team η m.p.side true (∅ : Finset W) place anchor
      (ApplyMF (Press.wickInput Z.scheme) (Stripped σ.team) σ letters) row ∧
    row = Trunk.unit ∧ ∀ j, row j = if j=0 then 1 else 0 := by
  intro row
  have physical := WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6RawDressing.physical Z matched m even (∅ : Finset W) place anchor η letters
  have cleared := vacant σ.team η m.p.side true place anchor _ row physical
  exact ⟨physical,cleared,fun j=>(congr_fun cleared j).trans (heat j)⟩
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialEmpty
