import YangMills.VolumeLimit

/-! Point values and smeared limits at a fixed physical period. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.Wilson

open Filter MeasureTheory Set
open scoped Topology

variable {g : GaugeGroup}

/-- Joint configurations strictly inside the displayed period. -/
def periodPatch (C : WilsonFamily g) (m n : ℕ) : Set (Points n) :=
  {z | z ∈ WilsonFamily.separated n ∧ ∀ i a,
    -((C.period m).val / (2 : ℝ)) < z i a ∧ z i a < (C.period m).val / (2 : ℝ)}

abbrev PeriodPointTable (C : WilsonFamily g) :=
  (m : ℕ) → {n : ℕ} → (Fin n → C.Token) → periodPatch C m n → ℂ

/-- Extension by zero is only a convention for integrating suitable tests. -/
def periodValue {C : WilsonFamily g} (F : PeriodPointTable C) (m : ℕ) {n : ℕ}
    (v : Fin n → C.Token) (z : Points n) : ℂ := by
  classical
  exact if hz : z ∈ periodPatch C m n then F m v ⟨z, hz⟩ else 0

def nodePosition (C : WilsonFamily g) (N m : ℕ) {n : ℕ}
    (x : Fin n → Site (C.period m * C.denominator N)) : Points n :=
  WithLp.toLp 2 fun i => C.place N m (x i)

structure FixedPointReturns (C : WilsonFamily g) (F : PeriodPointTable C) : Prop where
  regular (m n : ℕ) (v : Fin n → C.Token) : Continuous (F m v)
  tested (m n : ℕ) (v : Fin n → C.Token) (t : SeparatedTest n) (suitable : C.suitable m t) :
    Tendsto (fun N => C.smear N m v t) atTop (𝓝 (∫ z, t z * periodValue F m v z))
  fixedPeriod (m n : ℕ) (v : Fin n → C.Token) (K : Set (Points n))
      (compact : IsCompact K) (inside : K ⊆ periodPatch C m n) (ε : ℝ) (positive : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ z ∈ K, ∀ x : Fin n → Site (C.period m * C.denominator N),
        dist (nodePosition C N m x) z < δ →
        dist (C.finiteMoment N m v x) (periodValue F m v z) < ε

end YangMills.Wilson
