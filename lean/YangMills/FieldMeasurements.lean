import YangMills.StressTensor

/-! Measurements of free fields and phase differences on the physical field space. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.FixedFields
open Filter Set
open scoped Topology BigOperators
variable {g : GaugeGroup} {C : WilsonFamily g} (B : Maxwell.Reference g) (T : Hierarchy C)
/-- Each free derivative is determined by differentiating the independently
specified Wick moments with arbitrary separated spectators. -/
def WickDerivative {d : ℕ} (j : Axis) (v : B.sector d) (w : B.sector (d+1)) : Prop :=
  ∀ (n : ℕ) (q : Fin n → Σ e, B.sector e) (x : Points (n+1)), x ∈ separated _ →
    B.moment x (Fin.cons w.val (fun i => (q i).2.val)) =
      Ward.firstDerivative j (fun y => B.moment y (Fin.cons v.val (fun i => (q i).2.val))) x

/-- All sufficiently small positive radii, including those between the Maxwell
scales. Fields and their engineering degrees are fixed before taking the limit. -/
def PhaseBound : Prop :=
  ∀ (n : ℕ) (a : Fin n → T.Tag) (K : Set (Points n)), IsCompact K → K ⊆ separated n →
    ∀ δ : ℝ, 0 < δ → ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x ∈ K, ∀ s t : Option T.Character,
      ‖r ^ (∑ i, (a i).1) • (T.correlation s a (r • x) - T.correlation t a (r • x))‖ ≤ 2 * r ^ (1-δ)

structure Probe where
  n : ℕ
  spectators : Fin n → Σ e, B.sector e
  point : Points (n+1)
  separated : point ∈ YangMills.separated (n+1)

/-- Leading one-insertion measurements using a finite family of free probes
per degree suffice to identify a prescribed physical column. -/
def Separates (d : ℕ) (probes : Finset (Probe B)) : Prop :=
  ∀ v w : B.sector d, (∀ p ∈ probes, B.moment p.point (Fin.cons v.val (fun i => (p.spectators i).2.val)) =
    B.moment p.point (Fin.cons w.val (fun i => (p.spectators i).2.val))) → v = w

end YangMills.FixedFields
