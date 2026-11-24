import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6EmptyForest
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarArchive
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes

variable {G : Gauge} {W : Type} [LinearOrder W]
abbrev issued (P : W → MS.Land.Plaid (Press.portDeck G) 0) (w : W) :
    MS.Rake.Label (Press.portDeck G) := ⟨0,P w⟩
variable (A : MS_Data G (OpenAxis.Plot (Press.portDeck G))) (P : W → MS.Land.Plaid (Press.portDeck G) 0)
    (μ : ℝ) (x : W → QP) (injectiveX : Function.Injective x)
include injectiveX
theorem row (i : W) : ∃t : ℝ, MS.Theater.film (Press.portDeck G) (P i).2 (h:=0)=MvPolynomial.C (t:ℂ) ∧
    MS.Dial.spine A (issued P) μ x {i} =
      Rake.circle (MS.Tide.frameF Unit μ).η (MS.Wind.col (Ace.estate G t)) := by
  obtain ⟨t,h⟩ := Ace.cost0 (P i)
  refine ⟨t,h,?_⟩
  rw [(MS.Dial.pin A (issued P) μ injectiveX).2.1 i]
  unfold Rake.rowM
  exact congrArg (Rake.circle (MS.Tide.frameF Unit μ).η) (Ace.title A (P i) t h).symm
theorem income (i : W) (k : ℕ) : MS.Dial.book A (issued P) μ x {i} (k+1)=0 := by
  obtain ⟨t,_,actual⟩ := row A P μ x injectiveX i
  change MS.Vane.blade (MS.Dial.spine A (issued P) μ x {i} (k+1)) ()=0
  rw [actual]
  change limUnder atTop (fun _ : ℝ => (0:ℂ)) = 0
  exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℂ)) atTop (𝓝 0)).limUnder_eq
theorem original (i : W) (k : ℕ) : MS.Dial.tour A (issued P) μ x {i} (k+1)=0 := by
  let F := MS.Dial.book A (issued P) μ x
  let T := Trunk.stack (marked W)
  have one : T.wages F 1 = F := by
    simp only [Actors.wages,Actors.phase,Actors.power,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,T.identityR]
  change (∑ j∈Finset.range (1+1),T.wages F j) {i} (k+1)=0
  rw [Finset.sum_range_succ,Finset.sum_range_one,Pi.add_apply,Stencil.spare Trunk (Finset.singleton_nonempty i),zero_add,one]
  exact income A P μ x injectiveX i k
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarArchive
