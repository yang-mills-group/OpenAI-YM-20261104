import YM.MS.Graphical.DeepClusters
import YM.MS.Rake.Cluster

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Flux Landau Arts Arc Wire Rock Path Alps
open _root_.YM.MS.Shine Hem Mell Pearl Train Rake
open scoped Topology ContDiff Interval
variable {I: Type} [LinearOrder I] {G: Gauge}
structure Population (G : Gauge) (I : Type) where
  height : I→ℕ
  x : I → Tone.QP
  y : ℝ
  bulk : ℕ → Schedule G
  single : I → ℕ → Schedule G
namespace Population
variable {m n: ℕ} {X: Population G I} {s t: Finset I}
variable (X)
abbrev points : Position I Unit := fun i _=> X.x i
abbrev sepCost (s t : Finset I) := rootX X.points t () - rootX X.points s ()
abbrev budget (n : ℕ) (s : Finset I): ℕ := (∑ i ∈ s, X.height i)+ 2*n
abbrev groupedTree (bulk side : ℕ → Schedule G) (n : ℕ) := ∑ i ∈ Domain.paths n 0,
   treeAt (bulk (n-i)) (side i)
abbrev Packets (G : Gauge) (I : Type):= Finset I → ℕ→ Schedule G
def touchPair (T : Packets G I) (s t : Finset I) (n : ℕ) : Schedule G :=
  ∑ i ∈ antidiagonal n, joinAt (X.sepCost s t) X.y (T t i.1) (T (s \ t) i.2)
def links (side : ℕ→Schedule G) (T : Packets G I) (s : Finset I) (n : ℕ) :=
  groupedTree X.bulk side n + ∑ t ∈ picks s, touchPair X T s t n
def closeM (T : Packets G I) (s : Finset I) (n : ℕ) : Schedule G :=
  Nat.strongRecOn n (fun m h=> pinTower X.y (X.links (fun i => if h' : i < m then h i h' else 0) T s m) (X.budget m s))
def recursion (s : Finset I) (f : ∀ t:Finset I, t ⊂ s → ℕ→Schedule G) (n : ℕ) : Schedule G :=
  if h:s.Nonempty then
    if s.card<2 then X.single (s.min' h) n else X.closeM (fun t=> if h:t ⊂ s then f t h else 0) s n
  else 0
def clusters : Packets G I := fun s=> Finset.strongInductionOn s X.recursion
end Population
end YM.MS.Graphical
