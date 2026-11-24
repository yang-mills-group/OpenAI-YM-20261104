import YM.Integration.LocalComparisonInterface

/-!
The regular/caption part of the full local-comparison receipt has a genuine
uniform scalar readout.  Only the zeroth term of the factorial derivative
norm is needed, so no equality between the requested derivative order and
the physical representation's full order is assumed.

The price below is independent of torus volume and of every independently
chosen test.  It is a bound for the actual masked log in the given Deck.
It does not bound the quotient of the forced gas by its vacuum on flagged
fields; that separate integrated readout must retain the actual law.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker Finset Overlay RG3.Forms RG3.Script.Picnic
open scoped BigOperators Classical

variable {G : Gauge} {n : Side}

/-- Zeroth derivatives are included in the native factorial norm with
coefficient one.  This loses neither factorials nor field-order factors. -/
lemma grain_value {p : BudgetPoint} {S : Support n} {f : Config G n → ℂ}
    {o : Site n} {b : ℝ} (h : Mix.grain p S f o b)
    (U : Config G n) (hU : Healthy p.threshold S U) : ‖f U‖ ≤ b := by
  obtain ⟨a, ha, hsum, hderiv⟩ := h
  have hzero : a 0 ≤ b := by
    have hs := Finset.single_le_sum
      (f := fun i : ℕ => a i / (i.factorial : ℝ))
      (s := range (p.order + 1))
      (fun i _ => div_nonneg (ha i) (by positivity))
      (show 0 ∈ range (p.order + 1) by simp)
    have hs' : a 0 ≤ ∑ i ∈ range (p.order + 1), a i / (i.factorial : ℝ) := by
      simpa using hs
    exact hs'.trans hsum
  exact (hderiv [] (by simp) (by simp) U hU).trans hzero

/-- A variable per-root bill is summed only over the marker roots.
There is no sum over the ambient lattice sites. -/
lemma rooted_sumBudget {A V : Type*} [Fintype V] [DecidableEq V]
    {f : A → ℝ} {roots : A → Finset V} {b : V → ℝ}
    (hf : ∀ i, 0 ≤ f i) (hne : ∀ i, (roots i).Nonempty)
    (h : ∀ v, SumBudget (fun i => if v ∈ roots i then f i else 0) (b v)) :
    SumBudget f (∑ v, b v) := by
  let q (v : V) (i : A) := if v ∈ roots i then f i else 0
  have hs : Summable (fun i => ∑ v, q v i) :=
    summable_sum (s := univ) (f := q) (fun v _ => (h v).2.1)
  have hle (i : A) : f i ≤ ∑ v, q v i := by
    obtain ⟨v, hv⟩ := hne i
    calc
      f i = q v i := by simp only [q, if_pos hv]
      _ ≤ ∑ v, q v i := single_le_sum (fun v _ => (h v).1 i) (mem_univ v)
  have hf' : Summable f := hs.of_nonneg_of_le hf hle
  refine ⟨hf, hf', (hf'.tsum_le_tsum hle hs).trans ?_⟩
  rw [Summable.tsum_finsetSum (f := q) (fun v _ => (h v).2.1)]
  exact sum_le_sum (fun v _ => (h v).2.2)

variable {V : Type} {X : Type*} [Fintype V] [DecidableEq V]
    {R : Census V} {P : Rep G n} {o : V → Site n}
    {T : Taste X o P R} {p : BudgetPoint} {w : V → ℝ}
    {κ regularPrice forcedPrice : ℝ}

/-- The actual masked regular and caption log, uniformly over the entire
test family, is paid directly by the complete rooted regular receipt. -/
theorem FullBudget.log_price (h : FullBudget p T w κ regularPrice forcedPrice)
    (hthreshold : p.threshold = P.p.threshold) (x : X) (U : Config G n) :
    Poly.price w ((T.leaf x).log U) ≤ Fintype.card V * regularPrice := by
  choose B D hB hD htotal using h.regularTotal
  let r (i : ℕ) := Poly.toll w (T.menu.rays i) *
    p.mass (T.menu.branch i) (h.white i)
  let c (i : ℕ) := Poly.toll w (T.tag i) * p.mass (T.site i) (h.gold i)
  have hr : SumBudget r (∑ v, B v) := rooted_sumBudget
    (fun i => mul_nonneg (Poly.worth h.radii _).le
      ((h.white_nonnegative i).trans (p.loMass _ _ (h.white_nonnegative i))))
    (fun i => (h.active x).articles.proper i) hB
  have hc : SumBudget c (∑ v, D v) := rooted_sumBudget
    (fun i => mul_nonneg (Poly.worth h.radii _).le
      ((h.gold_nonnegative i).trans (p.loMass _ _ (h.gold_nonnegative i))))
    (fun i => (h.active x).captions.card i) hD
  have hray (i : ℕ) : Poly.price w ((T.leaf x).contents.ray i U) ≤ r i := by
    change Poly.price w (Poly.send (T.menu.rays i)
      (masked P.p.threshold (T.menu.branch i) (T.menu.regular x i) U)) ≤ _
    rw [Poly.solo]
    apply mul_le_mul_of_nonneg_left _ (Poly.worth h.radii _).le
    apply le_trans _ (p.loMass _ _ (h.white_nonnegative i))
    by_cases hU : Healthy P.p.threshold (T.menu.branch i) U
    · rw [masked_eq _ _ _ _ hU]
      obtain ⟨v, hv⟩ := (h.active x).articles.proper i
      exact grain_value ((h.regular i).controls x v hv) U (hthreshold.symm ▸ hU)
    rw [masked_ne _ _ _ _ hU, norm_zero]
    exact h.white_nonnegative i
  have hcaption (i : ℕ) :
      Poly.price w (Poly.send (T.tag i) (T.score x i)) ≤ c i := by
    rw [Poly.solo]
    exact mul_le_mul_of_nonneg_left
      ((h.caption x i).trans (p.loMass _ _ (h.gold_nonnegative i)))
      (Poly.worth h.radii _).le
  have hregular := Poly.budgeted h.radii hr.2.1 hray
  have hcaptions := Poly.budgeted h.radii hc.2.1 hcaption
  have hunits : Poly.price w (∑ v, Poly.send (R.fire v) (T.menu.global x v)) ≤
      ∑ v, w v * h.unitBound v := by
    apply (Poly.batch h.radii _ _).trans
    apply sum_le_sum
    intro v _
    rw [Poly.solo, Poly.solo_toll]
    exact mul_le_mul_of_nonneg_left (h.unit x v) (h.radii v).le
  change Poly.price w (((∑ v, Poly.send (R.fire v) (T.menu.global x v)) +
    ∑' i, (T.leaf x).contents.ray i U) + ∑' i, Poly.send (T.tag i) (T.score x i)) ≤ _
  apply (Poly.addition h.radii _ _).trans
  apply (add_le_add ((Poly.addition h.radii _ _).trans
    (add_le_add hunits (hregular.2.trans hr.2.2)))
    (hcaptions.2.trans hc.2.2)).trans
  rw [← sum_add_distrib, ← sum_add_distrib]
  exact (sum_le_sum (fun v _ => htotal v)).trans_eq (by simp)

/-- The finite nilpotent exponential of the actual log has the same
uniformity.  The forced gas is deliberately not cancelled here. -/
theorem FullBudget.pass_log_price (h : FullBudget p T w κ regularPrice forcedPrice)
    (hthreshold : p.threshold = P.p.threshold) (x : X) (U : Config G n) :
    Poly.price w (Poly.pass ((T.leaf x).log U)) ≤
      Real.exp (Fintype.card V * regularPrice) :=
  (Poly.pass_budget h.radii _).trans (Real.exp_monotone (h.log_price hthreshold x U))

/-- Every scalar coefficient of the actual log is controlled with the
announced independent marker radii; no volume norm equivalence is used. -/
theorem FullBudget.log_coefficient (h : FullBudget p T w κ regularPrice forcedPrice)
    (hthreshold : p.threshold = P.p.threshold) (x : X) (U : Config G n) (s : R.Mode) :
    ‖((T.leaf x).log U).part s‖ ≤
      (Fintype.card V * regularPrice) / Poly.toll w s := by
  rw [le_div_iff₀ (Poly.worth h.radii s), mul_comm]
  exact (Poly.member h.radii s _).trans (h.log_price hthreshold x U)

end YM.Integration.LocalComparison
