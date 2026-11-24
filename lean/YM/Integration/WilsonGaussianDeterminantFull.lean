import YM.Integration.PhysicalAffineScalarLogarithm
import YM.Integration.WilsonGaussianDeterminantRoster

/-! Sum of the retained determinant roots, the omitted seed roots, and the finite-window correction on the same physical Gram matrices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantFull

open LocalTaylorR2 LocalTaylorR2.Pavilion Analysis
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Mesh Port Work.G05 Animals Itinerary Reserves Census

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
variable {F : Forest S.ratio} {P : Teller G}

open PhysicalAffineScalarLogarithm
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
  {F : Forest S.ratio} {R : Rep G f} {W s μ C : ℝ} {P : Teller G}
  {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}

/-- Restricted trace omitted from the elastic head at the marked sites. -/
def seed (X : Coat T F) (i : Bond f) : ℝ :=
  if voyage X.seeds (200*X.B) i then X.condensation i else 0

/-- Difference of the two finite-window inverse errors at the same bond. -/
def correction (X : Coat T F) (i : Bond f) : ℝ :=
  (windowDifference X.shutter X.blank.plate i - windowDifference X.shutter X.plate i)/2

theorem rooted (H : Cash W s μ L Q o C T R) (X : Coat T F) (i : Bond f)
    (hx : X.x=s) (hw : X.width=o.K) (hm : X.manifest) :
    X.undercurrent i + seed X i - correction X i = fullPair X i := by
  have ticket := H.laws.data.localP F X hx hw hm
  have pair := stored X i ticket.sails.full ticket.empty.scale ticket.sails.scale
  change X.condensation i - fullPair X i = correction X i at pair
  have h : X.undercurrent i + seed X i = X.condensation i := by
    by_cases h : voyage X.seeds (200*X.B) i <;> simp [Coat.undercurrent,seed,h]
  rw [h]
  linarith only [pair]

theorem original (H : Cash W s μ L Q o C T R) (X : Coat T F)
    (hx : X.x=s) (hw : X.width=o.K) (hm : X.manifest) :
    (∑ i, (X.undercurrent i + seed X i - correction X i)) =
      (Real.log X.blank.plate.det - Real.log X.plate.det)/2 := by
  have ticket := H.laws.data.localP F X hx hw hm
  calc
    _ = ∑ i, fullPair X i := Finset.sum_congr rfl fun i _ => rooted H X i hx hw hm
    _ = _ := fullPair_sum X ticket.sails.full ticket.empty.scale ticket.sails.scale

end YM.Integration.WilsonGaussianDeterminantFull
end
