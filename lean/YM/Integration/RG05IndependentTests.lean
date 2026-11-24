import YM.RG05Readout.Nuclear.Pings

/-! The literal native joint of independently bounded E4 tests has one
uniform derivative bound. The factor depends only on derivative order and
slot count, and multiplies the original individual budgets. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.RG05IndependentTests

open Function Set RG05Readout RG05Readout.Native RG05Readout.Pulse RG05Readout.Nuclear
open scoped Topology ContDiff BigOperators Classical

variable {V : Type*} [Fintype V]

/-- A fixed combinatorial derivative factor, before any test is chosen. -/
def productCost (order count : ℕ) : ℝ := ((2 : ℝ) ^ order) ^ count

lemma tall_budget_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Complexion E} {d : ℕ} {c : ℝ} (h : Tall f d 1 c) : 0 ≤ c := by
  exact (norm_nonneg (iteratedFDeriv ℝ 0 f.val (0 : E))).trans
    (by simpa only [pow_zero, one_mul] using h 0 (Nat.zero_le d) 0)

def slot (i : V) (f : Body) : Wave V :=
  ⟨fun x => f.val (x i),
    (show ContDiff ℝ ∞ f.val from f.property).comp (contDiff_apply ℝ _ i)⟩

/-- Projection to a single original coordinate costs at most one in the
native maximum norm on the joint test domain. -/
theorem slot_tall (i : V) {f : Body} {d : ℕ} {c : ℝ}
    (h : Tall (E := E4) f d 1 c) : Tall (slot i f) d 1 c := by
  intro n hn x
  let P : Cloud V →L[ℝ] E4 := ContinuousLinearMap.proj i
  have hP : ‖P‖ ≤ 1 := P.opNorm_le_bound zero_le_one fun y => by
    change ‖y i‖ ≤ 1 * ‖y‖
    simpa only [one_mul] using norm_le_pi_norm y i
  change ‖iteratedFDeriv ℝ n (f.val ∘ P) x‖ ≤ _
  rw [P.iteratedFDeriv_comp_right (lit f d) x (by exact_mod_cast hn)]
  have he := (iteratedFDeriv ℝ n f.val (P x)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => P)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at he
  have hpow : ‖P‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg P) hP
  exact (he.trans ((mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans_eq
    (mul_one _))).trans (h n hn (x i))

private lemma joint_insert (i : V) (s : Finset V) (hi : i ∉ s) (f : V → Body) :
    joint (insert i s) f = chord (slot i (f i)) (joint s f) := by
  apply Subtype.ext
  funext x
  exact Finset.prod_insert hi

/-- Every finite collection retains its separate test budgets. Empty
collections are included, with product and combinatorial factor equal to one. -/
theorem joint_tall_finset (s : Finset V) (f : V → Body) (c : V → ℝ) (d : ℕ)
    (h : ∀ i ∈ s, Tall (E := E4) (f i) d 1 (c i)) :
    Tall (joint s f) d 1 (productCost d s.card * ∏ i ∈ s, c i) := by
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro h n hn x
      have he : (joint (∅ : Finset V) f).val = fun _ : Cloud V => (1 : ℂ) := by
        funext y
        change (∏ i ∈ (∅ : Finset V), (f i).val (y i)) = (1 : ℂ)
        exact Finset.prod_empty
      rw [he]
      simp only [productCost, Finset.card_empty, pow_zero, Finset.prod_empty, mul_one, one_pow]
      cases n with
      | zero => simp only [norm_iteratedFDeriv_zero, norm_one, le_refl]
      | succ n => rw [iteratedFDeriv_succ_const]; simp
  | @insert i s hi ih =>
      intro h
      have hiT := h i (Finset.mem_insert_self i s)
      have hsT := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have hb := threshold 1 (productCost d s.card * ∏ j ∈ s, c j)
        (slot_tall i hiT) hsT (tall_budget_nonneg hiT)
        (tall_budget_nonneg hsT) zero_le_one
      have he : (2 : ℝ) ^ d * c i * (productCost d s.card * ∏ j ∈ s, c j) =
          productCost d (insert i s).card * ∏ j ∈ insert i s, c j := by
        simp only [productCost, Finset.card_insert_of_notMem hi, Finset.prod_insert hi,
          pow_succ]
        ring
      rw [he] at hb
      rw [joint_insert i s hi f]
      exact hb

/-- Uniform native Wave seminorm for independent bounded input tests. -/
theorem joint_tall (f : V → Body) (c : V → ℝ) (d : ℕ)
    (h : ∀ i, Tall (E := E4) (f i) d 1 (c i)) :
    Tall (joint Finset.univ f) d 1
      (productCost d (Fintype.card V) * ∏ i, c i) := by
  simpa only [Finset.card_univ] using joint_tall_finset Finset.univ f c d (fun i _ => h i)

/-- Each actual joint-support point lies in every original factor support. -/
theorem joint_support (f : V → Body) {x : Cloud V}
    (hx : x ∈ tsupport (joint Finset.univ f).val) (i : V) :
    x i ∈ tsupport (f i).val := by
  have hclosed : IsClosed ((fun y : Cloud V => y i) ⁻¹' tsupport (f i).val) :=
    (isClosed_tsupport (f i).val).preimage (continuous_apply i)
  apply (closure_minimal (t := (fun y : Cloud V => y i) ⁻¹' tsupport (f i).val) ?_ hclosed) hx
  intro y hy
  apply subset_closure
  intro he
  apply hy
  exact Finset.prod_eq_zero (Finset.mem_univ i) he

/-- The support radius is inherited uniformly from the original factors. -/
theorem joint_shape (f : V → Body) {R : ℝ}
    (h : ∀ i, ∀ y ∈ tsupport (f i).val, ‖y‖ ≤ R) :
    ∀ x ∈ tsupport (joint Finset.univ f).val, ∀ i, ‖x i‖ ≤ R := by
  intro x hx i
  exact h i (x i) (joint_support f hx i)

/-- Separated original supports give separation of the whole joint Wave.
No assumption restricts repeated labels or compares independent test values. -/
theorem joint_separated (f : V → Body) {η : ℝ}
    (h : ∀ i j, i ≠ j → ∀ y ∈ tsupport (f i).val,
      ∀ z ∈ tsupport (f j).val, η ≤ ‖y - z‖) :
    ∀ x ∈ tsupport (joint Finset.univ f).val,
      ∀ i j, i ≠ j → η ≤ ‖x i - x j‖ := by
  intro x hx i j hij
  exact h i j hij (x i) (joint_support f hx i) (x j) (joint_support f hx j)

end YM.Integration.RG05IndependentTests
