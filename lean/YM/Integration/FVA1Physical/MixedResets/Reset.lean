import YM.Integration.FVA1Physical.MixedResets.Aggregate
import YM.Comparison.RG02.Adjacent.Caliber

/-!
# Coupling and field reset on the full cover prescription
No independent beta substitution on the physical evaluation! This prices
jets (purely coefficient identity, no norm bound in this file) in the new formal
units; used later on the same post-reset representation that is an input to
the next step. The calibrated kinetic ledger is supplied separately (and with
higher *vacuum* order).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Filter Function Finset Lattice RG Wilson Marker Precision Tree Input
open Push Uniform Next.SectorChange
open Comparison.RG02
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Ker
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port Progress.ClassicalKin Progress.ClassicalKin.Tent
open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {c : Side} {V : Type} [Fintype V] [DecidableEq V]
    {I : Marker.Census V} {ι ι' α : Type} {passport passport' : Passport c V}
    (C : Adjacent.Caliber) (q p : ℕ)

/-- Reexpress through order p, with q the typically higher order paid on the vacuum coupling. -/
def combineReset (bill : ℕ → α → rule (Coarse G) c → Poly I) (r : ℕ)
    (t : α) (z : rule (Coarse G) c) : Poly I :=
  Poly.inject fun m => Adjacent.born (fun i x => (bill i t x).part m) (C.back q) 0 p r z

theorem born_through {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U V : Adjacent.Display X} (h : ∀ i ≤ p, ∀ x, U i x = V i x) :
    Adjacent.born U (C.back q) 0 p = Adjacent.born V (C.back q) 0 p := by
  have eqC : Adjacent.cover U p = Adjacent.cover V p := by
    funext t x
    exact sum_congr rfl fun i hi => congr_arg _ (h i (mem_range_succ_iff.mp hi) x)
  funext i x
  unfold Adjacent.born Adjacent.ages
  rw [eqC]

/-- Our *same* cover step gives every outgoing orientation at the calibration bend. -/
theorem reset_renderer {rows : ι → Row passport I G α} {rows' : ι' → Row passport' I G α}
    {U U' : Layout G} {extra extra' : Finset Age} {grades : V → ℕ} {weights : V → ℝ} {pieces k : ℕ}
    {width funds : ℝ} {bill : ℕ → α → rule (Coarse G) c → Poly I}
    (paid : Earn.Scene.Armada rows' weights grades width funds p pieces k) (pos : 0 < width)
    (render : Renderer rows U extra grades p bill)
    (reset : ∀ r ≤ p, ∀ (t : α) z m,
      (Air.discharge (colorsOf rows' U' extra' grades t) r (tint G (Exterior.Body 1 c) (exteriorL G c z))).part m
        = Adjacent.born (fun i x => (Air.discharge (colorsOf rows U extra grades t) i (tint G (Exterior.Body 1 c)
            (exteriorL G c x))).part m) (C.back q) 0 p r z) :
    Renderer rows' U' extra' grades p (combineReset C q p bill) := by
  apply renderer_from_discharge paid pos
  intro r order t z
  ext1 m
  change _ = Adjacent.born (fun i x => (bill i t x).part m) (C.back q) 0 p r z
  rw [reset r order]
  apply congr_fun (congr_fun (born_through C q p _) r) z
  intro i hi x
  exact congr_arg (fun x : Poly I => x.part m) (render.coefficients i hi t x)
end YM.Integration.FVA1Physical.MixedResets
