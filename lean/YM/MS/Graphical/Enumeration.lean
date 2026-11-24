import YM.MS.Dock.Recipes
import YM.MS.Graphical.Ladder

set_option autoImplicit false
namespace YM.MS.Graphical.Diagram
open Set Filter Function Finset MeasureTheory
open Plane Koszul Heat Flux Landau Arts Arc Wire Rock Path Alps
open _root_.YM.MS.Shine Hem Mell Pearl Train Book Convolve Dock
open Motif Literal
open scoped Topology ContDiff BigOperators
/-- Enumerate all ordered connected tree joins. -/
def distributeS (S : Finset (ℕ×ℕ)) (L R : ℕ→ Multiset Diagram) : Multiset Diagram :=
   S.val.bind (fun p => (L p.1).bind (fun x => (R p.2).map (fun y => Diagram.merge x y)))
def tower (b : Bool) (h n : ℕ) (U : Multiset Diagram) :=
   Multiset.bind U (fun g => ladder g (rankRoom h b n))
noncomputable section
def truncateD {α : Type} [Zero α] (n : ℕ) (V : ∀ i, i<n → α) (i : ℕ) := if h:i<n then V i h else 0
/-- Enumerate (true-mode) ambient diagrams with positive coupling order and ladder bounds. -/
def ambient (n : ℕ) : Multiset Diagram := Nat.strongRecOn n (fun n f =>
   if n=0 then 0 else tower true 4 n ({lit n} + distributeS (shortB n) (truncateD n f) (truncateD n f)))
/-- Allocation with exactly one mark (recall we do *not* swap a mark to the other side
of a `merge`). `shortM n` allows a bulk operand of degree from `1` through `n`. -/
def insertions (h n : ℕ) : Multiset Diagram := Nat.strongRecOn n (fun n f =>
   tower false h n ({lit n} + distributeS (shortM n) ambient (truncateD n f)))
end
end YM.MS.Graphical.Diagram
