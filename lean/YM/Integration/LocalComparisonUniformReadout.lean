import YM.Integration.LocalComparisonReadout
import YM.Integration.ActualNormalizedComparison

/-!
The common coefficient majorants in FullBudget yield one positive polynomial
which dominates the actual masked regular/caption log for all independent
tests and all conditioning fields.  Thus the coefficient supremum can stay
inside the weighted sum.  No supremum/sum interchange and no torus-volume
norm equivalence is used.

This is the regular/caption factor of the full comparison.  It does not erase
the forced gas or supply the missing integrated forced-error estimate.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker Finset Overlay RG3.Forms RG3.Script.Picnic
open UniformPolynomialComparison
open scoped BigOperators Classical

section Algebra
variable {V A X : Type*} [DecidableEq V] {R : Census V}

private lemma positive_send (s : R.Mode) {b : ℝ} (hb : 0 ≤ b) :
    Positive (Poly.send s (b : ℂ)) := by
  intro q
  rw [Poly.part_send]
  split <;> simp [hb]

private lemma dominates_send (s : R.Mode) {f : X → ℂ} {b : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ b) :
    Dominates (Poly.send s (b : ℂ)) (fun x => Poly.send s (f x)) := by
  intro x q
  rw [Poly.part_send, Poly.part_send]
  split
  · exact hf x
  simp

private lemma positive_tsum {f : A → Poly R} (hf : Summable f)
    (hp : ∀ i, Positive (f i)) : Positive (∑' i, f i) := by
  intro q
  have hs : Summable (fun i => (f i).part q) := (Poly.get q).summable hf
  rw [Poly.share hf, Complex.re_tsum hs, Complex.im_tsum hs]
  refine ⟨tsum_nonneg (fun i => (hp i q).1), ?_⟩
  simp only [show ∀ i, ((f i).part q).im = 0 from fun i => (hp i q).2, tsum_zero]

private lemma positive_sum (s : Finset A) (f : A → Poly R)
    (hf : ∀ i ∈ s, Positive (f i)) : Positive (∑ i ∈ s, f i) := by
  intro q
  rw [Poly.part_sum]
  simp only [Complex.re_sum, Complex.im_sum]
  exact ⟨sum_nonneg (fun i hi => (hf i hi q).1),
    sum_eq_zero (fun i hi => (hf i hi q).2)⟩

private lemma dominates_add {a b : Poly R} {f g : X → Poly R}
    (hf : Dominates a f) (hg : Dominates b g) :
    Dominates (a + b) (fun x => f x + g x) := by
  intro x q
  rw [Poly.part_plus, Poly.part_plus, Complex.add_re]
  exact (norm_add_le _ _).trans (add_le_add (hf x q) (hg x q))

private lemma dominates_sum (s : Finset A) {a : A → Poly R} {f : A → X → Poly R}
    (hf : ∀ i ∈ s, Dominates (a i) (f i)) :
    Dominates (∑ i ∈ s, a i) (fun x => ∑ i ∈ s, f i x) := by
  intro x q
  rw [Poly.part_sum, Poly.part_sum, Complex.re_sum]
  exact (norm_sum_le _ _).trans (sum_le_sum (fun i hi => hf i hi x q))

private lemma dominates_tsum {a : A → Poly R} {f : A → X → Poly R}
    (ha : Summable a) (hf : ∀ x, Summable (fun i => f i x))
    (h : ∀ i, Dominates (a i) (f i)) :
    Dominates (∑' i, a i) (fun x => ∑' i, f i x) := by
  intro x q
  have hs : Summable (fun i => (a i).part q |>.re) :=
    Complex.reCLM.summable ((Poly.get q).summable ha)
  have hn : Summable (fun i => ‖(f i x).part q‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => h i x q)
  have hsa : Summable (fun i => (a i).part q) := (Poly.get q).summable ha
  rw [Poly.share (hf x), Poly.share ha, Complex.re_tsum hsa]
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun i => h i x q) hs)
end Algebra

variable {G : Gauge} {n : Side} {V : Type} {X : Type*}
    [Fintype V] [DecidableEq V] {R : Census V} {P : Rep G n} {o : V → Site n}
    {T : Taste X o P R} {p : BudgetPoint} {w : V → ℝ}
    {κ regularPrice forcedPrice : ℝ}

/-- The positive common coefficient polynomial is chosen before the tests
or the conditioning field. -/
def FullBudget.logMajorant (h : FullBudget p T w κ regularPrice forcedPrice) : Poly R :=
  ((∑ v, Poly.send (R.fire v) (h.unitBound v : ℂ)) +
    ∑' i, Poly.send (T.menu.rays i) (h.white i : ℂ)) +
    ∑' i, Poly.send (T.tag i) (h.gold i : ℂ)

-- Actual masked values are paid by the zeroth factorial component.
omit [Fintype V] in
private lemma masked_le (h : FullBudget p T w κ regularPrice forcedPrice)
    (hthreshold : p.threshold = P.p.threshold) (x : X) (U : Config G n) (i : ℕ) :
    ‖masked P.p.threshold (T.menu.branch i) (T.menu.regular x i) U‖ ≤ h.white i := by
  by_cases hU : Healthy P.p.threshold (T.menu.branch i) U
  · rw [masked_eq _ _ _ _ hU]
    obtain ⟨v, hv⟩ := (h.active x).articles.proper i
    exact grain_value ((h.regular i).controls x v hv) U (hthreshold.symm ▸ hU)
  rw [masked_ne _ _ _ _ hU, norm_zero]
  exact h.white_nonnegative i

/-- The original FullBudget witnesses dominate every coefficient uniformly,
with exactly the rooted regular price times the number of markers. -/
theorem FullBudget.log_majorant (h : FullBudget p T w κ regularPrice forcedPrice)
    (x₀ : X) (hthreshold : p.threshold = P.p.threshold) :
    Positive h.logMajorant ∧
    Dominates h.logMajorant (fun z : X × Config G n => (T.leaf z.1).log z.2) ∧
    Poly.price w h.logMajorant ≤ Fintype.card V * regularPrice := by
  choose B D hB hD htotal using h.regularTotal
  let r (i : ℕ) := Poly.toll w (T.menu.rays i) *
    p.mass (T.menu.branch i) (h.white i)
  let c (i : ℕ) := Poly.toll w (T.tag i) * p.mass (T.site i) (h.gold i)
  have hr : SumBudget r (∑ v, B v) := rooted_sumBudget
    (fun i => mul_nonneg (Poly.worth h.radii _).le
      ((h.white_nonnegative i).trans (p.loMass _ _ (h.white_nonnegative i))))
    (fun i => (h.active x₀).articles.proper i) hB
  have hc : SumBudget c (∑ v, D v) := rooted_sumBudget
    (fun i => mul_nonneg (Poly.worth h.radii _).le
      ((h.gold_nonnegative i).trans (p.loMass _ _ (h.gold_nonnegative i))))
    (fun i => (h.active x₀).captions.card i) hD
  have hradius (i : ℕ) :
      Poly.price w (Poly.send (T.menu.rays i) (h.white i : ℂ)) ≤ r i := by
    rw [Poly.solo, Complex.norm_real, Real.norm_of_nonneg (h.white_nonnegative i)]
    exact mul_le_mul_of_nonneg_left (p.loMass _ _ (h.white_nonnegative i))
      (Poly.worth h.radii _).le
  have hcaption (i : ℕ) :
      Poly.price w (Poly.send (T.tag i) (h.gold i : ℂ)) ≤ c i := by
    rw [Poly.solo, Complex.norm_real, Real.norm_of_nonneg (h.gold_nonnegative i)]
    exact mul_le_mul_of_nonneg_left (p.loMass _ _ (h.gold_nonnegative i))
      (Poly.worth h.radii _).le
  have hregular := Poly.budgeted h.radii hr.2.1 hradius
  have hcaptions := Poly.budgeted h.radii hc.2.1 hcaption
  have hregActual (z : X × Config G n) :
      Summable (fun i => (T.leaf z.1).contents.ray i z.2) := by
    refine (Poly.budgeted h.radii hr.2.1 (fun i => ?_)).1
    change Poly.price w (Poly.send (T.menu.rays i)
      (masked P.p.threshold (T.menu.branch i) (T.menu.regular z.1 i) z.2)) ≤ r i
    rw [Poly.solo]
    exact mul_le_mul_of_nonneg_left
      ((masked_le h hthreshold z.1 z.2 i).trans (p.loMass _ _ (h.white_nonnegative i)))
      (Poly.worth h.radii _).le
  have hcapActual (z : X × Config G n) :
      Summable (fun i => Poly.send (T.tag i) (T.score z.1 i)) := by
    refine (Poly.budgeted h.radii hc.2.1 (fun i => ?_)).1
    rw [Poly.solo]
    exact mul_le_mul_of_nonneg_left
      ((h.caption z.1 i).trans (p.loMass _ _ (h.gold_nonnegative i)))
      (Poly.worth h.radii _).le
  have hposU : Positive (∑ v, Poly.send (R.fire v) (h.unitBound v : ℂ)) :=
    positive_sum _ _ (fun v _ => positive_send _ (h.unit_nonnegative v))
  have hposR := positive_tsum hregular.1 (fun i => positive_send _ (h.white_nonnegative i))
  have hposC := positive_tsum hcaptions.1 (fun i => positive_send _ (h.gold_nonnegative i))
  refine ⟨(hposU.add hposR).add hposC, ?_, ?_⟩
  · change Dominates _ (fun z : X × Config G n =>
      ((∑ v, Poly.send (R.fire v) (T.menu.global z.1 v)) +
      ∑' i, (T.leaf z.1).contents.ray i z.2) +
      ∑' i, Poly.send (T.tag i) (T.score z.1 i))
    apply dominates_add
    · apply dominates_add
      · exact dominates_sum _ (fun v _ => dominates_send _ (fun z => h.unit z.1 v))
      · apply dominates_tsum hregular.1 hregActual
        intro i
        exact dominates_send _ (fun z => masked_le h hthreshold z.1 z.2 i)
    exact dominates_tsum hcaptions.1 hcapActual
      (fun i => dominates_send _ (fun z => h.caption z.1 i))
  have hunits : Poly.price w (∑ v, Poly.send (R.fire v) (h.unitBound v : ℂ)) ≤
      ∑ v, w v * h.unitBound v := by
    apply (Poly.batch h.radii _ _).trans
    apply sum_le_sum
    intro v _
    simp only [Poly.solo, Poly.solo_toll, Complex.norm_real,
      Real.norm_of_nonneg (h.unit_nonnegative v), le_refl]
  apply (Poly.addition h.radii _ _).trans
  apply (add_le_add ((Poly.addition h.radii _ _).trans
    (add_le_add hunits (hregular.2.trans hr.2.2)))
    (hcaptions.2.trans hc.2.2)).trans
  rw [← sum_add_distrib, ← sum_add_distrib]
  exact (sum_le_sum (fun v _ => htotal v)).trans_eq (by simp)

/-- The supremum over tests and fields remains inside every coefficient. -/
theorem FullBudget.uniform_log_price (h : FullBudget p T w κ regularPrice forcedPrice)
    (x₀ : X) (hthreshold : p.threshold = P.p.threshold) :
    uniformPrice w (fun z : X × Config G n => (T.leaf z.1).log z.2) ≤
      Fintype.card V * regularPrice := by
  obtain ⟨hpos, hdom, hprice⟩ := h.log_majorant x₀ hthreshold
  exact (uniformPrice_le hpos hdom h.radii).trans hprice

/-- Nonlinear regular/caption error in the full nilpotent polynomial,
still with the supremum inside the individual weighted coefficients. -/
theorem FullBudget.uniform_log_exponential_error
    (h : FullBudget p T w κ regularPrice forcedPrice)
    (x₀ : X) (hthreshold : p.threshold = P.p.threshold) :
    uniformPrice w (fun z : X × Config G n => Poly.pass ((T.leaf z.1).log z.2) - 1) ≤
      Real.exp (Fintype.card V * regularPrice) - 1 := by
  obtain ⟨hpos, hdom, hprice⟩ := h.log_majorant x₀ hthreshold
  exact (exponential_error_bound hpos hdom h.radii).trans
    (sub_le_sub_right (Real.exp_monotone hprice) 1)

end YM.Integration.LocalComparison
