import YM.MS.Graphical.Diagram

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical.Diagram
open Set Filter Function Finset MeasureTheory Metric
open Plane Koszul Heat Flux Landau Arts Arc Wire Rock Path Alps
open _root_.YM.MS.Shine Hem Mell Pearl Train Book Convolve
open Motif Literal
open scoped Topology ContDiff BigOperators Classical
variable {G: Gauge} {g: Diagram} {b: Bool} {h k: ℕ}
/-- For every tree split, also allow all contributing consecutive closes, with some
padding (0 through max **rank**, not number of possible closes). -/
def ladder (g : Diagram) (k : ℕ) : Multiset Diagram :=
    match k with
    | 0 => {g}
    | k+1 => {g} + ladder (close g) k
abbrev total {α A : Type} [AddCommMonoid A] (l : Multiset α) (f : α → A) : A := (l.map f).sum
variable (a: ℕ→ Mob G)
variable (h)
local notation "evalD" => evaluate G a h
def allPages (f : Multiset Diagram) (b : Bool) := total f (fun i => (evalD i b).pages)
end YM.MS.Graphical.Diagram
