import YM.Integration.WilsonGraphSeparatedShapeJets

noncomputable section
namespace YM.Integration.WilsonGraphCartesianJetBound

open Filter Finset
open scoped BigOperators
variable {n l : ℕ}

/-- The physical direction changes only the declared point and its actual Cartesian axis. -/
def axis (c : Fin n × YM.Axis) : YM.Points n :=
  PiLp.single 2 c.1 (YM.basis c.2)

/-- Decomposition on the issued four axes of every insertion, also for no insertions. -/
theorem expansion (u : YM.Points n) :
    ∑ c : Fin n × YM.Axis, u c.1 c.2 • axis c = u := by
  classical
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro j
  simp [axis, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ h
      simp [Ne.symm h]
    · simp
  · intro a _ h
    apply Finset.sum_eq_zero
    intro b _
    simp [Pi.single_eq_of_ne (Ne.symm h)]
  · simp

theorem entry_le (u : YM.Points n) (c : Fin n × YM.Axis) : ‖u c.1 c.2‖ ≤ ‖u‖ :=
  (PiLp.norm_apply_le (u c.1) c.2).trans (PiLp.norm_apply_le u c.1)

/-- Ordered basis expansion of the whole real multilinear operator, retaining repeated directions. -/
theorem cartesian (T : (YM.Points n [×l]→L[ℝ] ℂ)) (u : Fin l → YM.Points n) :
    T u = ∑ w : Fin l → Fin n × YM.Axis,
      (∏ i, u i (w i).1 (w i).2) • T (fun i => axis (w i)) := by
  classical
  calc
    T u = T (fun i => ∑ c : Fin n × YM.Axis, u i c.1 c.2 • axis c) :=
      congrArg T (funext fun i => (expansion (u i)).symm)
    _ = ∑ w : Fin l → Fin n × YM.Axis, T (fun i => u i (w i).1 (w i).2 • axis (w i)) :=
      T.toMultilinearMap.map_sum (fun i c => u i c.1 c.2 • axis c)
    _ = _ := Finset.sum_congr rfl fun w _ =>
      T.toMultilinearMap.map_smul_univ (fun i => u i (w i).1 (w i).2) (fun i => axis (w i))

/-- Summing the actual word constants controls the operator norm with the identical error factor. -/
theorem bound (T : (YM.Points n [×l]→L[ℝ] ℂ)) (C : (Fin l → Fin n × YM.Axis) → ℝ)
    (hC : ∀ w, 0 ≤ C w) {err : ℝ} (herr : 0 ≤ err)
    (h : ∀ w, ‖T (fun i => axis (w i))‖ ≤ C w * err) :
    ‖T‖ ≤ (∑ w, C w) * err := by
  classical
  apply T.opNorm_le_bound (mul_nonneg (Finset.sum_nonneg fun w _ => hC w) herr)
  intro u
  rw [cartesian T u]
  calc
    ‖∑ w : Fin l → Fin n × YM.Axis, (∏ i, u i (w i).1 (w i).2) •
        T (fun i => axis (w i))‖ ≤ ∑ w : Fin l → Fin n × YM.Axis,
        ‖(∏ i, u i (w i).1 (w i).2) • T (fun i => axis (w i))‖ := norm_sum_le _ _
    _ ≤ ∑ w : Fin l → Fin n × YM.Axis, (∏ i, ‖u i‖) * (C w * err) := by
      apply Finset.sum_le_sum
      intro w _
      rw [norm_smul, norm_prod]
      exact mul_le_mul (Finset.prod_le_prod (fun i _ => norm_nonneg _)
        (fun i _ => entry_le (u i) (w i))) (h w) (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = ((∑ w : Fin l → Fin n × YM.Axis, C w) * err) * ∏ i, ‖u i‖ := by
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- A single eventual scale and a single nonnegative constant work for every order through j,
    every actual center and every filed input. The dependent selector I can contain all those data. -/
theorem uniform {α : Type*} {I : α → Type*} (F : Filter α) (j : ℕ)
    (T : (s : α) → I s → (l : Fin (j + 1)) → (YM.Points n [×l.val]→L[ℝ] ℂ))
    (err : (s : α) → I s → ℝ) (herr : ∀ s u, 0 ≤ err s u)
    (one : ∀ (l : Fin (j + 1)) (w : Fin l.val → Fin n × YM.Axis),
      ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ s in F, ∀ u : I s,
        ‖T s u l (fun i => axis (w i))‖ ≤ D * err s u) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in F, ∀ (u : I s) (l : Fin (j + 1)),
      ‖T s u l‖ ≤ A * err s u := by
  classical
  choose D nonnegative paid using one
  let price (l : Fin (j + 1)) := ∑ w : Fin l.val → Fin n × YM.Axis, D l w
  have price_nonneg l : 0 ≤ price l := Finset.sum_nonneg fun w _ => nonnegative l w
  refine ⟨∑ l, price l, Finset.sum_nonneg fun l _ => price_nonneg l, ?_⟩
  have every : ∀ᶠ s in F, ∀ (l : Fin (j + 1)) (w : Fin l.val → Fin n × YM.Axis) (u : I s),
      ‖T s u l (fun i => axis (w i))‖ ≤ D l w * err s u :=
    Filter.eventually_all.mpr fun l => Filter.eventually_all.mpr (paid l)
  filter_upwards [every] with s all
  intro u l
  exact (bound (T s u l) (D l) (nonnegative l) (herr s u) (fun w => all l w u)).trans
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ => price_nonneg i) (Finset.mem_univ l)) (herr s u))

/-- The coordinate rows of a difference are the differences of the original rows at
    every order for which both of the actual operands are differentiable. -/
theorem residual {j : ℕ} (l : Fin (j + 1)) {actual predicted : YM.Points n → ℂ}
    {x : YM.Points n} (ha : ContDiffAt ℝ j actual x) (hp : ContDiffAt ℝ j predicted x)
    (w : Fin l.val → Fin n × YM.Axis) :
    (iteratedFDeriv ℝ l.val (fun y => actual y - predicted y) x) (fun i => axis (w i)) =
      (iteratedFDeriv ℝ l.val actual x) (fun i => axis (w i)) -
      (iteratedFDeriv ℝ l.val predicted x) (fun i => axis (w i)) := by
  have h : l.val ≤ j := Nat.le_of_lt_succ l.isLt
  have hl : (l.val : WithTop ℕ∞) ≤ (j : WithTop ℕ∞) := by exact_mod_cast h
  change iteratedFDeriv ℝ l.val (actual - predicted) x _ = _
  rw [iteratedFDeriv_sub_apply (ha.of_le hl) (hp.of_le hl)]
  rfl

/-- All original Cartesian-word estimates and local differentiability on the same field
    and prediction yield the full public operator-norm shape estimate with one scale. -/
theorem original {α : Type*} {I : α → Type*} (F : Filter α) (j : ℕ)
    (actual predicted : (s : α) → I s → YM.Points n → ℂ)
    (point : (s : α) → I s → YM.Points n) (err : (s : α) → I s → ℝ)
    (herr : ∀ s u, 0 ≤ err s u)
    (smooth : ∀ᶠ s in F, ∀ u : I s,
      ContDiffAt ℝ j (actual s u) (point s u) ∧ ContDiffAt ℝ j (predicted s u) (point s u))
    (rows : ∀ (l : Fin (j+1)) (w : Fin l.val → Fin n × YM.Axis),
      ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ s in F, ∀ u : I s,
        ‖(iteratedFDeriv ℝ l.val (actual s u) (point s u)) (fun i => axis (w i)) -
          (iteratedFDeriv ℝ l.val (predicted s u) (point s u)) (fun i => axis (w i))‖
          ≤ D * err s u) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in F, ∀ u : I s,
      YangMills.Matching.shapeJetEstimateAt j (actual s u) (predicted s u) (point s u)
        (A * err s u) := by
  let T (s : α) (u : I s) (l : Fin (j+1)) :=
    iteratedFDeriv ℝ l.val (fun y => actual s u y - predicted s u y) (point s u)
  obtain ⟨A, nonnegative, income⟩ := uniform F j T err herr (by
    intro l w
    obtain ⟨D, hD, paid⟩ := rows l w
    refine ⟨D, hD, ?_⟩
    filter_upwards [smooth, paid] with s hs hp
    intro u
    change ‖(iteratedFDeriv ℝ l.val (fun y => actual s u y - predicted s u y) (point s u))
      (fun i => axis (w i))‖ ≤ _
    rw [residual l (hs u).1 (hs u).2 w]
    exact hp u)
  refine ⟨A, nonnegative, ?_⟩
  filter_upwards [smooth, income] with s hs paid
  intro u
  refine ⟨(hs u).1, (hs u).2, ?_⟩
  intro l hl
  exact paid u ⟨l, Nat.lt_succ_of_le hl⟩

end YM.Integration.WilsonGraphCartesianJetBound


