import YangMills.CorrelationHierarchy

/-! Finite nesting of the physical OPE. At every internal vertex we evaluate
the same physical coefficient function on its child centers. Summing a separate
physical channel at every non-root vertex gives the iterated truncation. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Hierarchy

open Filter Set Function
open scoped Topology BigOperators Classical

/-- A finite rooted tree with labelled leaves. Vertex 0 is the root, the other
internal vertices are numbered by `Fin branches`. -/
structure FusionTree where
  leaves : ℕ
  branches : ℕ
  parent : Fin (branches+1) → Fin (branches+1)
  attachLeaf : Fin leaves → Fin (branches+1)
  rootFixed : parent 0 = 0
  reachesRoot (v) : ∃ n : ℕ, parent^[n] v = 0

namespace FusionTree
variable (t : FusionTree)

abbrev Vertex := Fin (t.branches+1)
abbrev Child (v : t.Vertex) := {u : Fin t.leaves ⊕ Fin t.branches //
  Sum.elim t.attachLeaf (fun i : Fin t.branches => t.parent i.succ) u = v}

noncomputable instance childFinite (v : t.Vertex) : Fintype (t.Child v) :=
  Fintype.ofFinite _

def ratio (s : t.Vertex → ℝ) (i : Fin t.branches) : ℝ := s i.succ / s (t.parent i.succ)

def positions {v : t.Vertex} (x : Fin t.leaves → Spacetime) (z : t.Vertex → Spacetime)
    (u : t.Child v) : Spacetime :=
  Sum.elim x (fun i : Fin t.branches => z i.succ) u.val

variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

def leafWeight (a : Fin t.leaves → T.Tag) (v : t.Vertex) : ℝ :=
  ∑ i : Fin t.leaves, if ∃ n : ℕ, t.parent^[n] (t.attachLeaf i) = v then ((a i).1 : ℝ) else 0

def cutoffGain (D : Fin t.branches → ℕ) (s : t.Vertex → ℝ) : ℝ :=
  ∑ i : Fin t.branches, (t.ratio s i)^(D i + 1)

abbrev Selection (D : Fin t.branches → ℕ) :=
  (v : Fin t.branches) → Σ j : Fin (D v + 1), T.Channel j.val

def vertexChannel {D : Fin t.branches → ℕ} (u : t.Selection T D)
    (w : ℕ) (c : T.Channel w) : t.Vertex → Σ j, T.Channel j :=
  Fin.cases ⟨w, c⟩ fun i => ⟨(u i).1.val, (u i).2⟩

def childField {D : Fin t.branches → ℕ} (a : Fin t.leaves → T.Tag)
    (u : t.Selection T D) {v : t.Vertex} (p : t.Child v) : T.Tag :=
  Sum.elim a (fun i : Fin t.branches => ⟨(u i).1.val, T.channelField _ (u i).2⟩) p.val

/-- Finite contraction of the actual coefficient at each vertex. Truncating a
child changes neither its center nor the locations of the other inputs. -/
def iterated (a : Fin t.leaves → T.Tag) (x : Fin t.leaves → Spacetime)
    (z : t.Vertex → Spacetime) (D : Fin t.branches → ℕ) (w : ℕ) (c : T.Channel w) : ℂ :=
  ∑ u : t.Selection T D, ∏ v : t.Vertex,
    let channel := t.vertexChannel T u w c v
    T.coefficient (t.childField T a u (v := v)) channel.1 channel.2 (t.positions x z) (z v)
end FusionTree


end YangMills.Hierarchy
