import YangMills.CorrelationHierarchy

/-! Geometric error of the *same* physical OPE, in fixed physical fields.
The perturbative order is a separate truncation parameter. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Hierarchy

open Filter Set
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

/-- Physical coefficient and spectator bounds for one shrinking cluster.
For a fixed physical exterior, take its singleton as `K`. -/
structure SeparatedPowerLog : Prop where
  coefficient {I : Type} [Fintype I] (a : I → T.Tag) (w : ℕ) (i : T.Channel w)
      (o : Spacetime) (M η : ℝ) (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧ ∃ k : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ x, Within r M η x o → ‖T.coefficient a w i x o‖ ≤
        A * r ^ ((w : ℝ) - T.weight a) * (1 + |Real.log r|)^k
  remainder {I J : Type} [Fintype I] [Fintype J] (a : I → T.Tag) (b : J → T.Tag)
      (h : ℕ) (o : Spacetime) (M η c : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (hc : 0 < c)
      (K : Set (J → Spacetime)) (compact : IsCompact K) (clear : ∀ y ∈ K, Clear o y c) :
    ∃ A : ℝ, 0 < A ∧ ∃ k : ℕ, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x, Within r M η x o →
      ∀ y ∈ K, ∀ s, ‖T.grouped s a x b y - T.truncatedWithSpectators h s a x o b y‖ ≤
        A * r ^ ((h : ℝ) + 1 - T.weight a) * (1 + |Real.log r|)^k

end YangMills.Hierarchy
