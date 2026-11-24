import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedFilm
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedMeteor
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedCurrency
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes
variable {G : Gauge}
def entered (u : MS.Rake.Label (Press.portDeck G)) : Labels.Pol G :=
  match u with | ⟨h,P⟩=> MS.Theater.film (Press.portDeck G) P.2 (h:=h)
theorem original (A : MS_Data G (OpenAxis.Plot (Press.portDeck G))) (μ : ℝ) (h n : ℕ) (x : Stage n)
    (t : Fin n→Dframe.Toon G h) (w : Fin n) (grade : (t w).size=0) :
    ∀ k,Equator.wave μ A h n x k (Dframe.fill t)=((Dframe.theory (t w)).val.coeff 0) *
      Landing.moondye μ A (Dframe.flash ∘ t) (Finset.univ.erase w) k x.val := by
  let u:=Dframe.flash ∘ t
  obtain ⟨P,c,submitted,physical,paid⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedFilm.original A u μ (Arrival.Schedule.plot x.val) (Arrival.Schedule.track x.property) w grade
  have raw : entered (u w)=MvPolynomial.C (c:ℂ) := by
    rw [submitted]
    exact physical
  have label : (Dframe.theory (t w)).val=MvPolynomial.C (c:ℂ) := by
    change Maxwell.reduceEq (entered (u w))=_
    rw [raw]
    exact (Maxwell.reduceEq (G:=G)).commutes (c:ℂ)
  have zero : (Dframe.theory (t w)).val.coeff 0=(c:ℂ) := by
    exact (congrArg (MvPolynomial.coeff 0) label).trans (by simp)
  intro k
  change Dframe.meteor μ A h x.val k (Dframe.fill t)=_
  rw [Dframe.ribbon,zero]
  change MS.Dial.tour A u μ (Arrival.Schedule.plot x.val) Finset.univ k=(c:ℂ)*MS.Dial.tour A u μ (Arrival.Schedule.plot x.val) (Finset.univ.erase w) k
  have actual:=paid (Finset.univ.erase w) (Finset.notMem_erase w _) k
  simpa only [Finset.insert_erase (Finset.mem_univ w)] using actual
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6MarkedCurrency
