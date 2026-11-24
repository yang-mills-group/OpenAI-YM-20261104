import YangMills.PhysicalOPE.Tree

/-! Physical finite-tree fusion with an arbitrarily small power loss at each scale. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Hierarchy

open Filter MeasureTheory Set
open scoped Topology BigOperators Classical

namespace FusionTree
variable (t : FusionTree)

abbrev Node := Fin t.leaves ⊕ t.Vertex

def location (x : Fin t.leaves → Spacetime) (z : t.Vertex → Spacetime) : t.Node → Spacetime :=
  Sum.elim x z

def below (u : t.Node) (v : t.Vertex) : Prop :=
  ∃ n : ℕ, t.parent^[n] (Sum.elim t.attachLeaf id u) = v

def inChild {v : t.Vertex} (p : t.Child v) (u : t.Node) : Prop :=
  Sum.elim (fun i => u = .inl i) (fun j : Fin t.branches => t.below u j.succ) p.val

/-- Each subtree fits in its parent's ball. Distinct child subtrees are separated
at the parent scale, including their leaf positions and internal centers. -/
def separatedAt (r M η : ℝ) (s : t.Vertex → ℝ) (x : Fin t.leaves → Spacetime)
    (z : t.Vertex → Spacetime) : Prop :=
  s 0 = r ∧ (∀ v, 0 < s v) ∧ (∀ i : Fin t.branches, s i.succ ≤ s (t.parent i.succ)) ∧
  ∀ v, (∀ u, t.below u v → ‖t.location x z u - z v‖ ≤ M * s v) ∧
    ∀ p q : t.Child v, p ≠ q → ∀ u w, t.inChild p u → t.inChild q w →
      η * s v ≤ ‖t.location x z u - t.location x z w‖

def clearOf {J : Type} (x : Fin t.leaves → Spacetime) (z : t.Vertex → Spacetime)
    (y : J → Spacetime) (δ : ℝ) : Prop :=
  (∀ u j, δ ≤ ‖t.location x z u - y j‖) ∧ ∀ i j : J, i ≠ j → δ ≤ ‖y i - y j‖

variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

/-- The engineering power and the loss at the root and at every child/parent ratio. -/
def powerBound (out ε : ℝ) (a : Fin t.leaves → T.Tag) (s : t.Vertex → ℝ) : ℝ :=
  s 0 ^ (out - T.weight a - ε) *
    ∏ i : Fin t.branches, t.ratio s i ^ (-t.leafWeight T a i.succ - ε)

end FusionTree

/-- Test two functions against every integrable complex weight, with a uniform bound
on the error. Point masses recover the pointwise estimates. -/
structure TestedDifference {X : Type} [MeasurableSpace X] (μ : Measure X)
    (q first second : X → ℂ) (bound : ℝ) : Prop where
  firstIntegrable : Integrable (fun i => q i * first i) μ
  secondIntegrable : Integrable (fun i => q i * second i) μ
  error : ‖(∫ i, q i * first i ∂μ) - ∫ i, q i * second i ∂μ‖ ≤ (∫ i, ‖q i‖ ∂μ) * bound

variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

/-- All internal cutoffs are fixed before the outer radius tends to zero. Positions,
centers and spectator fields are read from the selected continuum hierarchy. -/
structure PowerTreeExpansion : Prop where
  coefficients (t : FusionTree) (a : Fin t.leaves → T.Tag) (D : Fin t.branches → ℕ)
      (w : ℕ) (c : T.Channel w) (M η ε : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε)
      (X : Type) [MeasurableSpace X] :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (s : t.Vertex → ℝ) (μ : Measure X) (q : X → ℂ),
      Integrable q μ → ∀ (x : X → Fin t.leaves → Spacetime) (z : X → t.Vertex → Spacetime),
      AEMeasurable x μ → AEMeasurable z μ →
      (∀ᵐ i ∂μ, q i ≠ 0 → t.separatedAt r M η s (x i) (z i)) →
      let flat := fun i => T.coefficient a w c (x i) (z i 0)
      let nested := fun i => t.iterated T a (x i) (z i) D w c
      let bound := t.powerBound T w ε a s
      ‖∫ i, q i * flat i ∂μ‖ ≤ (∫ i, ‖q i‖ ∂μ) * bound ∧
        TestedDifference μ q flat nested (bound * t.cutoffGain D s)
  spectators (t : FusionTree) (a : Fin t.leaves → T.Tag) {J : Type} [Fintype J]
      (b : J → T.Tag) (h : ℕ) (M η ε δ : ℝ) (hM : 0 ≤ M) (hη : 0 < η)
      (hε : 0 < ε) (hδ : 0 < δ) (X : Type) [MeasurableSpace X] :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (s : t.Vertex → ℝ) (μ : Measure X) (q : X → ℂ),
      Integrable q μ → ∀ (x : X → Fin t.leaves → Spacetime) (z : X → t.Vertex → Spacetime)
      (y : X → J → Spacetime), AEMeasurable x μ → AEMeasurable z μ → AEMeasurable y μ →
      (∀ᵐ i ∂μ, q i ≠ 0 → t.separatedAt r M η s (x i) (z i) ∧ t.clearOf (x i) (z i) (y i) δ) →
      ∀ phase : Option (X → T.Character), (∀ χ ∈ phase, AEMeasurable χ μ) →
        TestedDifference μ q (fun i => T.grouped (phase.map (· i)) a (x i) b (y i))
          (fun i => T.truncatedWithSpectators h (phase.map (· i)) a (x i) (z i 0) b (y i))
          (t.powerBound T ((h : ℝ) + 1) ε a s)

end YangMills.Hierarchy
