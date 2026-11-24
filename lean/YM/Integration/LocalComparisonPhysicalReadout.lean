import YM.Integration.LocalComparisonUniformReadout
import YM.Integration.LocalComparisonRelativeReadout

/-!
Physical nonlinear readout for products of independent input envelopes.
The actual log and its nilpotent exponential are retained.  Dividing the
marker radii by the per-slot input costs accounts for all disjoint products
exactly, including mixed coefficients.  Arbitrary positive mode prices are
not silently treated as multiplicative.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker Finset RG3.Forms RG3.Script.Picnic
open UniformPolynomialComparison
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] {R : Census V}

theorem envelopeProduct_positive {cost : V → ℝ} (hcost : ∀ v, 0 < cost v)
    (s : R.Mode) : 0 < envelopeProduct cost s :=
  prod_pos (fun v _ => hcost v)

/-- Disjoint marker products carry exactly the product of their original
analytic input envelopes. -/
theorem envelopeProduct_merge (cost : V → ℝ) {a b s : R.Mode}
    (h : Poly.merges a b s) :
    envelopeProduct cost s = envelopeProduct cost a * envelopeProduct cost b := by
  unfold envelopeProduct
  rw [← h.2, prod_union h.1]

theorem restoreEnvelope_product_mul (cost : V → ℝ) (hcost : ∀ v, 0 < cost v)
    (A B : Poly R) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost) (A * B) =
      restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost) A *
      restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost) B := by
  ext s
  change (envelopeProduct cost s : ℂ) * (A * B).part s = _
  rw [Poly.part_mul, Poly.part_mul, mul_sum]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro b _
  by_cases h : Poly.merges a b s
  · rw [if_pos h, if_pos h]
    change (envelopeProduct cost s : ℂ) * (A.part a * B.part b) =
      ((envelopeProduct cost a : ℂ) * A.part a) *
      ((envelopeProduct cost b : ℂ) * B.part b)
    rw [envelopeProduct_merge cost h, Complex.ofReal_mul]
    ring
  rw [if_neg h, if_neg h, mul_zero]

theorem restoreEnvelope_product_one (cost : V → ℝ) (hcost : ∀ v, 0 < cost v) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost) (1 : Poly R) = 1 := by
  ext s
  change (envelopeProduct cost s : ℂ) * (1 : Poly R).part s = (1 : Poly R).part s
  rw [Poly.one_part]
  by_cases hs : s = R.quiet
  · subst s
    simp [envelopeProduct, Census.quiet]
  simp [hs]

theorem restoreEnvelope_product_pow (cost : V → ℝ) (hcost : ∀ v, 0 < cost v)
    (A : Poly R) (k : ℕ) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost) (A ^ k) =
      (restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost) A) ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using restoreEnvelope_product_one cost hcost
  | succ k ih =>
    rw [pow_succ, restoreEnvelope_product_mul cost hcost, ih, pow_succ]

section
variable [Fintype V]

theorem restoreEnvelope_product_pass (cost : V → ℝ) (hcost : ∀ v, 0 < cost v)
    (A : Poly R) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost) (Poly.pass A) =
      Poly.pass (restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost) A) := by
  unfold Poly.pass
  rw [map_sum]
  apply sum_congr rfl
  intro k _
  rw [map_smul, restoreEnvelope_product_pow cost hcost]
end

/-- Exact price identity, with no finite-dimensional norm equivalence. -/
theorem restoreEnvelope_product_price (cost w : V → ℝ) (hcost : ∀ v, 0 < cost v)
    (A : Poly R) :
    Poly.price (fun v => w v / cost v)
      (restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost) A) =
      Poly.price w A := by
  unfold Poly.price
  apply sum_congr rfl
  intro s _
  change Poly.toll (fun v => w v / cost v) s *
    ‖(envelopeProduct cost s : ℂ) * A.part s‖ = _
  have hp := envelopeProduct_positive hcost s
  have ht : Poly.toll (fun v => w v / cost v) s =
      Poly.toll w s / envelopeProduct cost s := by
    simp only [Poly.toll, envelopeProduct, prod_div_distrib]
  rw [ht, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le]
  field_simp

private theorem restored_positive (cost : R.Mode → ℝ) (hcost : ∀ s, 0 < cost s)
    {A : Poly R} (hA : Positive A) : Positive (restoreEnvelope cost hcost A) := by
  intro s
  change 0 ≤ ((cost s : ℂ) * A.part s).re ∧ ((cost s : ℂ) * A.part s).im = 0
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  exact ⟨mul_nonneg (hcost s).le (hA s).1, by rw [(hA s).2, mul_zero]⟩

variable [Fintype V] {G : Gauge} {n : Side} {X : Type*} {P : Rep G n} {o : V → Site n}
    {T : Taste X o P R} {p : BudgetPoint} {w cost : V → ℝ}
    {κ regularPrice forcedPrice : ℝ}

/-- One positive common majorant for the original physical log, with all
per-slot input costs kept in the effective radii. -/
theorem RelativeBudget.physical_log_majorant
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) (x₀ : X) (hthreshold : p.threshold = P.p.threshold) :
    ∃ A : Poly R, Positive A ∧
      Dominates A (fun z : X × Config G n => (T.leaf z.1).log z.2) ∧
      Poly.price (fun v => w v / cost v) A ≤ Fintype.card V * regularPrice := by
  obtain ⟨hp, hd, hb⟩ := h.budget.log_majorant x₀ hthreshold
  let E : Poly R ≃L[ℂ] Poly R :=
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost)
  refine ⟨E h.budget.logMajorant, restored_positive _ _ hp, ?_, ?_⟩
  · intro z s
    have he := congrArg (fun A : Poly R => A.part s)
      (restoreEnvelope_log T (envelopeProduct cost) (envelopeProduct_positive hcost) z.1 z.2)
    change (envelopeProduct cost s : ℂ) * _ = _ at he
    change ‖((T.leaf z.1).log z.2).part s‖ ≤
      ((envelopeProduct cost s : ℂ) * h.budget.logMajorant.part s).re
    rw [← he, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (envelopeProduct_positive hcost s).le]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left (hd z s) (envelopeProduct_positive hcost s).le
  exact (restoreEnvelope_product_price cost w hcost _).trans_le hb

/-- Actual physical log price, uniform coefficient by coefficient over
all independent tests and all conditioning fields. -/
theorem RelativeBudget.physical_uniform_log_price
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) (x₀ : X) (hthreshold : p.threshold = P.p.threshold) :
    uniformPrice (fun v => w v / cost v)
      (fun z : X × Config G n => (T.leaf z.1).log z.2) ≤
      Fintype.card V * regularPrice := by
  obtain ⟨A, hp, hd, hb⟩ := h.physical_log_majorant hcost x₀ hthreshold
  exact (uniformPrice_le hp hd (fun v => div_pos (h.budget.radii v) (hcost v))).trans hb

/-- Nonlinear actual physical regular/caption error.  The forced gas is
still retained as the separate physical readout obligation. -/
theorem RelativeBudget.physical_uniform_log_exponential_error
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) (x₀ : X) (hthreshold : p.threshold = P.p.threshold) :
    uniformPrice (fun v => w v / cost v)
      (fun z : X × Config G n => Poly.pass ((T.leaf z.1).log z.2) - 1) ≤
      Real.exp (Fintype.card V * regularPrice) - 1 := by
  obtain ⟨A, hp, hd, hb⟩ := h.physical_log_majorant hcost x₀ hthreshold
  exact (exponential_error_bound hp hd (fun v => div_pos (h.budget.radii v) (hcost v))).trans
    (sub_le_sub_right (Real.exp_monotone hb) 1)

/-- A canonical admissible independent test tuple, used only to certify
that the whole test family is nonempty. -/
def zeroIndependentTests (D : V → ComparisonDensity.Address.Orbit) : IndependentTests D :=
  fun v => ⟨0, ComparisonDensity.Address.Orbit.Bill.zero.more (by norm_num)⟩

/-- Direct application to the independently chosen unit test functions of
the local-comparison interface, without an extra nonemptiness hypothesis. -/
theorem independent_test_log_exponential_error
    {D : V → ComparisonDensity.Address.Orbit} {T₀ : Taste (TestSpace D) o P R}
    (h : RelativeBudget p (pullback (testInclusion D) T₀) w κ (envelopeProduct cost)
      regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) (hthreshold : p.threshold = P.p.threshold) :
    uniformPrice (fun v => w v / cost v)
      (fun z : IndependentTests D × Config G n =>
        Poly.pass ((T₀.leaf (testInclusion D z.1)).log z.2) - 1) ≤
      Real.exp (Fintype.card V * regularPrice) - 1 :=
  h.physical_uniform_log_exponential_error hcost (zeroIndependentTests D) hthreshold

end YM.Integration.LocalComparison
