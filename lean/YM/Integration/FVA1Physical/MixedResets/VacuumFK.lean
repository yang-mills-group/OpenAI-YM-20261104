import YM.Integration.FVA1Physical.MixedResets.Thermodynamic
import YM.QuadraticLocal.Fk.Attire
import YM.Comparison.RG02.Symmetry.Code
import YM.AllOrder.Floe.Voyage

/-!
# Prescription (vacuum)

Tile-normalize the prescribed RG02 Wilson action, *not* logmarks,
*including* the infrared price at order zero. A single step:
all path data, extra curvature action, clip and Wilson kernel parameters fixed.
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
open scoped Classical Topology BigOperators
variable {G : Gauge} (P : Patch) (K : KernelChoices) (O : ChartRatio G)
  (action : PathData G) (clip : Clip) (U : Layout G) (extra : Finset Age)
  (p r : ℕ) {c f : Side} {S : StepData c f} {V : Type} [Fintype V] [DecidableEq V]

/-- Complete RG02 action coefficient at order r, working through order p,
all of the given vacuum action plan included. `colors.vac` overwritten from that plan.
When we bind the bills, can use the full marked datum itself (no dependence
of this bill on its nonquiet entries). -/
def vacuumFK {R : Marker.Census V} (colors : Bulk.Colors R G f)
    (g : Bulk.Kernel S clip action O) (F : Forest S.ratio) (t : S.Choices) (z : rule (Coarse G) c) : ℂ :=
  Symmetry.Orbit.ground g F t (QuadraticLocal.Fk.grant U extra colors) p r
    (tint G (Exterior.Body 1 c) (exteriorL G c z))

/-- All coefficients independent of this unmarked census. -/
def unmarked : Marker.Census Empty := ⟨Finset.univ, mem_univ _, fun _ => mem_univ _, fun _ _ _ => mem_univ _⟩

/-- RG02 bill on the finite Wick regulator. Zero on inadmissibly small tori where no such
formal kernel exists; choice of kernel irrelevant on large tori (lemmas below). -/
def vacuumBill : ComplexBill (Coarse G) := fun n =>
  if h : Nonempty (Bulk.Kernel (dock P K n) clip action O) then
    vacuumFK O action clip U extra p r (Bulk.Colors.noHole G (below P n) unmarked)
      h.some (trees P K n) (label (dock P K n))
  else 0

/-- **Cover step** in the action on a replicated torus (still pre-reset coupling). -/
def coverAction (z : rule (Coarse G) c) : ℂ :=
  onCover (vacuumBill P K O action clip U extra p r) z

open AllOrder.Floe.Step.PlanV Pressure Gauge
open RG.Supply Push.PriceCompiler AbsoluteSums ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Pane
open Bid Org Further.PhysicalPeriodLimitF933

variable {assets : Metals G} {D : Rolls assets.p}
  {cal : Roots (G := G) assets.p.profile assets.K assets.p.kernel} {x y k : ℕ} {hx : 4 ≤ x}

variable (income : Income D cal x y hx k) (card : Card D cal x y hx k)
include income

/-- A true auxiliary Fk kernel exists for the prescription, *at every* admitted torus size.
Obtained just as in `Aviary.sponsored`. No shared-kernel/cover limit assumption. -/
theorem kernel_exists {c : Side} (hc : Ad G (Mural.sheet assets.p D hx) assets.p.kernel c) :
    Nonempty (Bulk.Kernel (dock (Mural.sheet assets.p D hx) assets.p.kernel c) (assets.p.profile x).clip card.self.north assets.O) := by
  choose sol hsol using fun f : Forest (dock (Mural.sheet assets.p D hx) assets.p.kernel c).ratio =>
    income.frame.graph f card.self.upCost hc rfl rfl
  refine ⟨⟨sol, assets.oga, hc.1, fun f => (hsol f).critical, ⟨_, _, _, card.self.upCost⟩, fun f => ?_⟩⟩
  let estimate := income.frame.full_pack (B:=f) (label (dock (Mural.sheet assets.p D hx) assets.p.kernel c)) card.self.upCost hc rfl rfl
  exact ⟨_, estimate.2.1, estimate.1⟩
end YM.Integration.FVA1Physical.MixedResets
