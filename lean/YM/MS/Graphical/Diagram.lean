import YM.MS.Graphical.Block
import YM.MS.Graphical.Lines
import YM.MS.Motif.Receipt

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Metric
open Plane Koszul Heat Flux Landau Arts Arc Wire Rock Path Alps
open _root_.YM.MS.Shine Hem Mell Pearl Train Book Convolve
open Motif Literal
open scoped Topology ContDiff BigOperators Classical
/-- Recursive allocation of scale-ordered edges over exponent vertices (or a
single marked vertex and any number of exponent vertices, in `false` mode).
Connected, no stand-alone free propagator case. A `Diagram` describes a whole
family, not a fully-labelled incidence graph. -/
inductive Diagram
  | lit (order : ℕ)
  | close (left : Diagram)
  | merge (left right : Diagram)
  deriving DecidableEq
namespace Diagram
variable {G: Gauge}
/-- For running either the bulk or arbitrary-mark interpretation.
Unmarked families don't depend on `a` or `h`. -/
def dimTarget (h : ℕ) (b : Bool) := if b then 4 else h
def top (G : Gauge) (a : ℕ → Mob G) (b : Bool) (n : ℕ) : Coat G :=
   fun _ => if b then pulseX G n else a n
def fee (b : Bool) : ℂ := if b then 2⁻¹ else 1
/-- Graph integrals, UV limit and pole insertions. `a`: bare single-mark kernels
by order; unmarked vertices are fixed (`pulseX`), independent of `a` and of
the mark height `h`. A bridge does not give a complex-dimension loop increment.
A close does. For the estimates flow-by-flow, see `ordered`. -/
def evaluate (G : Gauge) (a : ℕ → Mob G) (h : ℕ) : Diagram → Bool → SectorFamily G
 | lit n, b => ⟨Finsupp.single 0 (top G a b n),0⟩
 | close g,b => integrateRen (dimTarget h b) (closeForce (evaluate G a h g b).pages)
 | merge g l,b => integrateRen (dimTarget h b) (fee b • bridgeForce (evaluate G a h g true).pages
                 (evaluate G a h l b).pages)
variable {a: ℕ→Mob G} {b: Bool} {h: ℕ}
/-- No transcendental rank guesses. A bulk vertex uses positive coupling degree
so a linear budget suffices for all the joins to lower-rank children. -/
def rankRoom (h : ℕ) (b : Bool) (order : ℕ) : ℕ := 2*order + if b then 2 else h
end Diagram
end YM.MS.Graphical
