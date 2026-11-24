import YangMills.PhysicalOPE.Tree
import YangMills.PhysicalOPE.SingleCluster

/-! Polylogarithmic bounds for physical fusion at separated scales. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Hierarchy
open Filter Set Function
open scoped Topology BigOperators Classical
namespace FusionTree
variable (t : FusionTree) {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
def occupied : Prop := ∀ v, ∃ i n, t.parent^[n] (t.attachLeaf i) = v

/-- Children lie in a bounded, separated shape at the declared vertex radius.
All allowed ratios can tend independently to zero. -/
def Admissible (r β M η : ℝ) (s : t.Vertex → ℝ) (x : Fin t.leaves → Spacetime)
    (z : t.Vertex → Spacetime) : Prop :=
  t.occupied ∧ s 0 = r ∧ (∀ v, 0 < s v) ∧ (∀ i, t.ratio s i ≤ β) ∧
    ∀ v, Within (s v) M η (t.positions (v := v) x z) (z v)

/-- Root power, child/parent engineering factors, and a single product of logs
over internal vertices, as in the uniform finite nesting estimate. -/
def bound (out : ℝ) (a : Fin t.leaves → T.Tag) (s : t.Vertex → ℝ) (k : ℕ) : ℝ :=
  s 0 ^ (out - T.weight a) *
  (∏ i : Fin t.branches, (t.ratio s i) ^ (-(t.leafWeight T a i.succ))) *
  ∏ v : t.Vertex, (1 + |Real.log (s v)|)^k

end FusionTree

variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

/-- Polylogarithmic factorization and spectator bounds for finite physical fusion trees.
The geometric bounds use the same exact coefficient representative at every vertex. -/
structure SeparatedNestedPowerLog : Prop where
  expansion (t : FusionTree) (a : Fin t.leaves → T.Tag) (D : Fin t.branches → ℕ)
      (w : ℕ) (c : T.Channel w) (M η : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (o : Spacetime) :
    ∃ β ∈ Set.Ioo (0 : ℝ) 1, ∃ A : ℝ, 0 < A ∧ ∃ k : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ s x z, t.Admissible r β M η s x z → z 0 = o →
        ‖T.coefficient a w c x o‖ ≤ A * t.bound T w a s k ∧
        ‖T.coefficient a w c x o - t.iterated T a x z D w c‖ ≤
          A * t.bound T w a s k * t.cutoffGain D s
  remainder (t : FusionTree) (a : Fin t.leaves → T.Tag) {J : Type} [Fintype J]
      (b : J → T.Tag) (h : ℕ) (o : Spacetime) (M η c : ℝ) (hM : 0 ≤ M)
      (hη : 0 < η) (hc : 0 < c) (K : Set (J → Spacetime)) (compact : IsCompact K)
      (clear : ∀ y ∈ K, Clear o y c) :
    ∃ β ∈ Set.Ioo (0 : ℝ) 1, ∃ A : ℝ, 0 < A ∧ ∃ k : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ s x z, t.Admissible r β M η s x z → z 0 = o → ∀ y ∈ K, ∀ phase,
        ‖T.grouped phase a x b y - T.truncatedWithSpectators h phase a x o b y‖ ≤
          A * t.bound T ((h : ℝ) + 1) a s k

end YangMills.Hierarchy
