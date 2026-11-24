import YM.Integration.LocalComparisonInterface

/-! Read a complete common-representation budget with different tests on different
labels. Each regular row may use a different healthy field and direction list at every
derivative order. The test for that row is fixed across its factorial sum. -/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical

open Lattice Wilson RG Marker RG3.Script.Picnic LocalComparison Push.AbsoluteSums
open scoped BigOperators

variable {G : Gauge} {n : Side}

/-- Field data for one factorial derivative reading at its stated support and root. -/
structure DerivativeTest (p : BudgetPoint) (S : Support n) (o : Site n) (G : Gauge) where
  field : ℕ → Config G n
  directions : ℕ → List (Directions G n)
  length j : j ≤ p.order → (directions j).length = j
  admitted j : j ≤ p.order → Healthy p.threshold S (field j)
  bounded j : j ≤ p.order → ∀ A ∈ directions j, p.dirBound o A

def DerivativeTest.read {p : BudgetPoint} {S : Support n} {o : Site n}
    (D : DerivativeTest p S o G) (f : Config G n → ℂ) : ℝ :=
  ∑ j ∈ Finset.range (p.order + 1), ‖leftDerivs f (D.directions j) (D.field j)‖ / j.factorial

theorem DerivativeTest.read_nonneg {p : BudgetPoint} {S : Support n} {o : Site n}
    (D : DerivativeTest p S o G) (f : Config G n → ℂ) : 0 ≤ D.read f :=
  Finset.sum_nonneg fun _ _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)

theorem DerivativeTest.read_le {p : BudgetPoint} {S : Support n} {o : Site n}
    (D : DerivativeTest p S o G) {f : Config G n → ℂ} {b : ℝ}
    (h : Mix.grain p S f o b) : D.read f ≤ b := by
  obtain ⟨budget, _, total, control⟩ := h
  apply le_trans (Finset.sum_le_sum ?_) total
  intro j hj
  have hd : j ≤ p.order := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have len := D.length j hd
  have hval := control (D.directions j) (by rwa [len]) (D.bounded j hd) (D.field j) (D.admitted j hd)
  exact div_le_div_of_nonneg_right (by simpa only [len] using hval) (Nat.cast_nonneg _)

variable {I : Type} [DecidableEq I] {R : Census I} {X : Type*}
    {P : Rep G n} {p : BudgetPoint} {o : I → Site n} {T : Taste X o P R}
    {w : I → ℝ} {κ regularPrice forcedPrice : ℝ}

/-- Unit, regular, caption and divided forced charges on the stated representation.
The regular and caption sums share their price. The forced sum retains its actual divisor.
All sums range over the full countable label families. -/
theorem tested_full_budget (H : FullBudget p T w κ regularPrice forcedPrice) (v : I)
    (unitTest : X) (reg cap : ℕ → X) (force : ℕ × ℕ → X)
    (field : ℕ × ℕ → Config G n)
    (jet : ∀ i, DerivativeTest p (T.menu.branch i) (o v) G) :
    (∃ b c : ℝ,
      SumBudget (fun i => if v ∈ (T.menu.rays i).val then Poly.toll w (T.menu.rays i) *
        p.mass (T.menu.branch i) ((jet i).read (T.menu.regular (reg i) i)) else 0) b ∧
      SumBudget (fun i => if v ∈ (T.tag i).val then Poly.toll w (T.tag i) *
        p.mass (T.site i) ‖T.score (cap i) i‖ else 0) c ∧
      w v * ‖T.menu.global unitTest v‖ + b + c ≤ regularPrice) ∧
    SumBudget (fun i : ℕ × ℕ => if v ∈ (T.menu.marks i.1 i.2).val then
      Poly.toll w (T.menu.marks i.1 i.2) * p.mass (P.activities.forced i.1).support
        ‖T.menu.force (force i) i.1 i.2 (field i)‖ else 0) (κ * forcedPrice) := by
  have cmp {mode : R.Mode} {s : Support n} {a b : ℝ} (hab : a ≤ b) :
      Poly.toll w mode * p.mass s a ≤ Poly.toll w mode * p.mass s b :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hab (Real.exp_nonneg _))
      (Poly.worth H.radii mode).le
  have pos {mode : R.Mode} {s : Support n} {a : ℝ} (ha : 0 ≤ a) :
      0 ≤ Poly.toll w mode * p.mass s a :=
    mul_nonneg (Poly.worth H.radii mode).le (mul_nonneg (Real.exp_nonneg _) ha)
  obtain ⟨b, c, regular, caption, total⟩ := H.regularTotal v
  refine ⟨⟨b, c, budget_mono regular ?_ ?_, budget_mono caption ?_ ?_, ?_⟩,
    budget_mono (H.forcedTotal v) ?_ ?_⟩
  · intro i
    split <;> first | exact pos ((jet i).read_nonneg _) | exact le_rfl
  · intro i
    split_ifs with h
    · exact cmp ((jet i).read_le ((H.regular i).controls (reg i) v h))
    · exact le_rfl
  · intro i
    split <;> first | exact pos (norm_nonneg _) | exact le_rfl
  · intro i
    split_ifs <;> first | exact cmp (H.caption (cap i) i) | exact le_rfl
  · have bound := mul_le_mul_of_nonneg_left (H.unit unitTest v) (H.radii v).le
    linarith
  · intro i
    split <;> first | exact pos (norm_nonneg _) | exact le_rfl
  · intro i
    split_ifs <;> first | exact cmp (H.forced (force i) i.1 i.2 (field i)) | exact le_rfl

end YM.Integration.FVA1Physical
