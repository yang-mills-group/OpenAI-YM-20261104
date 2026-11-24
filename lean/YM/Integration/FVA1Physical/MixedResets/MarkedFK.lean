import YM.QuadraticLocal.Sunrise.Fruit
import YM.Integration.FVA1Physical.MixedResets.VacuumFK

/-!
# Prescription on genuine mixed inputs

An impulse for *each participating incoming analytic interaction*. Distinct
inputs can be placed at different (or the same) sites. Relative to the group
links we put exactly the analytic log inserts, with powers and stencil positions
including the fine offsets. Thus upstairs the pins are source profiles on the
tile, **for all these interactions at once**, not a sequence of singleton
vacua. We use this prescription even when an interaction's atom contains a
winding path (use its supplied lift). `kernel_exists` is used only in the
*theorem*. All this is done on the formal branch; read `FullBudget` separately
on masked atoms.
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
open QuadraticLocal.Sunrise
open scoped Classical Topology BigOperators
variable {G : Gauge} {P : Patch} (K : KernelChoices) (O : ChartRatio G)
  (action : PathData G) (clip : Clip) (U : Layout G) (extra : Finset Age)
  {p : ℕ} {c f : Side} {S : StepData c f} {V : Type} [Fintype V] [DecidableEq V]

/-- Order-r *ordinary* (not derivative, not raw Markov numerator) coupling coefficient
of the full connected marked log, at all-slots monomial. -/
def connectedFK (p r : ℕ) (g : Bulk.Kernel S clip action O)
    (F : Forest S.ratio) (t : S.Choices) (budget : V → Loan)
    (atoms : ∀ i : V, Atom G (budget i).r) (locate : V → Site c → Site f)
    (z : rule (Coarse G ⊕ V) c) : ℂ :=
  let w := desks (Coarse G) V c z
  (Order.observe (Focus.census V) p
    (Order.logMarked (Bulk.Fk g F t (Balcony.displayC budget atoms locate U extra w.2)
      (tint G (Exterior.Body 1 c) (exteriorL G c w.1)) p)) r).part (Focus.onto (univ:Finset V))

variable (budget : V → Loan) (atoms : ∀ i : V, Atom G (budget i).r) (offset : V → Site P.L)

/-- Tile location convention: block-coordinate assembly. -/
def fineLocate (P : Patch) (off : V → Site P.L) (c : Side) (i : V) (z : Site c) : Site (below P c) :=
  (shores P c).assemble (z, off i)

def connectedBill (P : Patch) (offset : V → Site P.L) (p r : ℕ) : ComplexBill (Coarse G ⊕ V) := fun n =>
  if h : Nonempty (Bulk.Kernel (dock P K n) clip action O) then
    connectedFK O action clip U extra p r
      h.some (trees P K n) (label (dock P K n)) budget atoms (fineLocate P offset n)
  else 0

def coverImpulse (p r : ℕ) (w : rule V c) (u : rule (Coarse G) c) : ℂ :=
  onCover (connectedBill K O action clip U extra budget atoms P offset p r) (mingle u w)
end YM.Integration.FVA1Physical.MixedResets
