import YM.Integration.LocalComparisonPackets
import YM.Integration.LocalComparisonReadout

/-!
The existing analytic-packet payment convention supplies the finite formal
multiplier bound. Every genuine nonlinear slot has norm at most two on the
compact group. The coupling powers remain inside the original packet bill;
there is no inverse-radius or additional inverse-coupling payment.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Function Finset Lattice Wilson RG Marker
open Comparison.Density.RenderM
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
    {D : V → ComparisonDensity.Address.Orbit} {R : Census V}

omit [DecidableEq V] in
private theorem token_value_bound {r : ℕ}
    (T : Token G n (fun v => (D v).Mood) r) (x : TestSpace D)
    (hcoin : (∑ j, ‖T.gem j x‖) ≤ T.coin) (U : Config G n) :
    ‖T.read x U‖ ≤ (2 : ℝ) ^ r * T.coin := by
  have hslot (i : Fin r) (j : G.ColorIndex) :
      |(T.path i).atSite U T.root j| ≤ 2 := by
    rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [OrthonormalBasis.norm_eq_one, one_mul]
    exact Slot.eval_norm ..
  have hprod (j : Chroma (G := G) r) :
      |∏ i : Fin r, (T.path i).atSite U T.root (j i)| ≤ (2 : ℝ) ^ r := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : Fin r, (2 : ℝ) := prod_le_prod
        (fun _ _ => abs_nonneg _) (fun i _ => hslot i (j i))
      _ = _ := by simp
  unfold Token.read Token.touch
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : Chroma (G := G) r, (2 : ℝ) ^ r * ‖T.gem j x‖ := by
      apply sum_le_sum
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hprod j) (norm_nonneg _)
    _ = (2 : ℝ) ^ r * ∑ j, ‖T.gem j x‖ := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcoin (by positivity)

private theorem rooted_nonzero_sumBudget {A : Type*} [Fintype V]
    {f : A → ℝ} {roots : A → Finset V} {b : V → ℝ}
    (hf : ∀ i, 0 ≤ f i) (hne : ∀ i, f i ≠ 0 → (roots i).Nonempty)
    (h : ∀ v, SumBudget (fun i => if v ∈ roots i then f i else 0) (b v)) :
    SumBudget f (∑ v, b v) := by
  let q (v : V) (i : A) := if v ∈ roots i then f i else 0
  have hs : Summable (fun i => ∑ v, q v i) :=
    summable_sum (s := univ) (f := q) (fun v _ => (h v).2.1)
  have hle (i : A) : f i ≤ ∑ v, q v i := by
    by_cases hi : f i = 0
    · rw [hi]
      exact sum_nonneg (fun v _ => (h v).1 i)
    · obtain ⟨v, hv⟩ := hne i hi
      calc
        f i = q v i := by simp only [q, if_pos hv]
        _ ≤ ∑ v, q v i := single_le_sum (fun v _ => (h v).1 i) (mem_univ v)
  have hf' : Summable f := hs.of_nonneg_of_le hf hle
  refine ⟨hf, hf', (hf'.tsum_le_tsum hle hs).trans ?_⟩
  rw [Summable.tsum_finsetSum (f := q) (fun v _ => (h v).2.1)]
  exact sum_le_sum (fun v _ => (h v).2.2)

variable [Fintype V]
    {M : MarkedPackets D G n R} {p : BudgetPoint}
    {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {coverOffset coverSlope : ℕ}

/-- Full unmasked packet value, uniformly over independent unit tests and
all group fields. All original coupling powers are already paid in `Paid`. -/
theorem MarkedPackets.Paid.read_price
    (h : M.Paid p address region w g width budget coverOffset coverSlope)
    (x : IndependentTests D) (U : Config G n) :
    Poly.price w (M.read (testInclusion D x) g U) ≤
      (2 : ℝ) ^ M.rankCap * (Fintype.card V * budget) := by
  let q (i : ℕ) : ℝ := match M.packet i with
    | none => 0
    | some T => Poly.toll w (M.mode i) * ‖(g : ℂ) ^ M.power i‖ *
        T.coin * Real.exp (width * T.fall)
  have hq0 i : 0 ≤ q i := by
    cases hi : M.packet i with
    | none => simp only [q, hi, le_refl]
    | some T =>
      simp only [q, hi]
      exact mul_nonneg (mul_nonneg
        (mul_nonneg (Poly.worth h.positive _).le (norm_nonneg _))
        (h.coefficient i T hi).1) (Real.exp_pos _).le
  have hne i : q i ≠ 0 → (M.mode i).val.Nonempty := by
    intro hqi
    cases hi : M.packet i with
    | none => exact False.elim (hqi (by simp [q, hi]))
    | some T =>
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hz
      apply M.marked i T hi
      apply Subtype.ext
      exact hz
  have hq : SumBudget q (Fintype.card V * budget) := by
    have hr (v : V) : SumBudget (fun i => if v ∈ (M.mode i).val then q i else 0) budget := by
      convert h.roots v using 1
      funext i
      split_ifs
      · cases hi : M.packet i <;> simp only [q, hi]
      · rfl
    simpa using rooted_nonzero_sumBudget hq0 hne hr
  have hterm (i : ℕ) :
      Poly.price w (Poly.send (M.mode i) (M.term (testInclusion D x) g U i)) ≤
        (2 : ℝ) ^ M.rankCap * q i := by
    cases hi : M.packet i with
    | none => simp [MarkedPackets.term, q, hi]
    | some T =>
      have hc := (h.coefficient i T hi).1
      have hv := token_value_bound T (testInclusion D x) ((h.coefficient i T hi).2 x) U
      have hpow : (2 : ℝ) ^ M.rank i ≤ (2 : ℝ) ^ M.rankCap :=
        pow_le_pow_right₀ (by norm_num) (M.rank_bounded i T hi)
      have he : 1 ≤ Real.exp (width * T.fall) :=
        Real.one_le_exp (mul_nonneg h.width_pos.le (Nat.cast_nonneg _))
      have hread : ‖T.read (testInclusion D x) U‖ ≤
          (2 : ℝ) ^ M.rankCap * (T.coin * Real.exp (width * T.fall)) := by
        calc
          _ ≤ (2 : ℝ) ^ M.rank i * T.coin := hv
          _ ≤ (2 : ℝ) ^ M.rankCap * T.coin := mul_le_mul_of_nonneg_right hpow hc
          _ ≤ ((2 : ℝ) ^ M.rankCap * T.coin) * Real.exp (width * T.fall) :=
            le_mul_of_one_le_right (mul_nonneg (by positivity) hc) he
          _ = _ := by ring
      simp only [MarkedPackets.term, hi, Poly.solo, norm_mul, q]
      calc
        _ ≤ Poly.toll w (M.mode i) *
            (‖(g : ℂ) ^ M.power i‖ *
              ((2 : ℝ) ^ M.rankCap * (T.coin * Real.exp (width * T.fall)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hread (norm_nonneg _)) (Poly.worth h.positive _).le
        _ = _ := by ring
  have hs := hq.2.1.mul_left ((2 : ℝ) ^ M.rankCap)
  have hp := Poly.budgeted h.positive hs hterm
  exact hp.2.trans (by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hq.2.2 (by positivity))

/-- The literal full formal exponential has one finite multiplier payment.
This is an application of the existing packet-size convention, not a new
assumption on the represented residual or captured column. -/
theorem MarkedPackets.Paid.multiplier_price
    (h : M.Paid p address region w g width budget coverOffset coverSlope)
    (x : IndependentTests D) (U : Config G n) :
    Poly.price w (Poly.pass (M.read (testInclusion D x) g U)) ≤
      Real.exp ((2 : ℝ) ^ M.rankCap * (Fintype.card V * budget)) :=
  (Poly.pass_budget h.positive _).trans (Real.exp_monotone (h.read_price x U))

end YM.Integration.LocalComparison
