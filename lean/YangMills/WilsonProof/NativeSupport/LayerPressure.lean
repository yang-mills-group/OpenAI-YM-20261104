import YangMills.WilsonProof.NativeSupport.ActualNearBonds

/-! A uniform, intensive pressure comparison for the actual tagged path.
It permits a positive source depending on the entire fine field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Finset MeasureTheory Lattice RG Wilson Tree RGComparison.Core16 YM.Pressure
open WilsonUniformUnmarkedInletEnergySites WilsonUniformUnmarkedInletConnectedCovariance
open WilsonUniformUnmarkedInletSignedResponse
open scoped Classical BigOperators
variable {G : Gauge} {n c : Side}

private def springs {n : Side} : {c : Side} → (d : Descent n c) → Finset (sites n d)
  | _, .nil => ∅
  | _, .push _ _ d => univ.disjSum (springs d)

private lemma native_le (d : Descent n c) : c.val ≤ n.val := by
  induction d with
  | nil => rfl
  | @push m i S T d ih =>
    apply le_trans _ ih
    rw [S.ratio.exact_size]
    exact Nat.le_mul_of_pos_right _ S.ratio.count.property

private lemma spring_count (d : Descent n c) :
    (springs d).card ≤ d.depth * (n.val^4 * 4) := by
  induction d with
  | nil => simp [springs, Descent.depth]
  | @push m i S T d ih =>
    change (univ.disjSum (springs d)).card ≤ (d.depth+1)*_
    rw [card_disjSum, card_univ, add_mul, one_mul, add_comm (d.depth*_)]
    apply Nat.add_le_add _ ih
    simp only [Bond, Fintype.card_prod, site_card, Axis, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (native_le (.push S T d)) 4)

private lemma in_springs (d : Descent n c) (q : sites n d) (h : lag d q < d.depth) :
    q ∈ springs d := by
  induction d with
  | nil => exact (Nat.not_lt_zero _ h).elim
  | @push m i S T d ih =>
    rcases q with b | b
    · exact inl_mem_disjSum.mpr (mem_univ _)
    · exact inr_mem_disjSum.mpr (ih b (Nat.lt_of_succ_lt_succ h))

theorem count_interior (d : Descent n c) :
    (interior d).card ≤ d.depth * (n.val^4 * 4) :=
  (card_le_card fun q hq => in_springs d q (mem_filter.mp hq).2.2).trans (spring_count d)

private lemma score_cap (d : Descent n c) (v : ℕ → ℝ) (top : v d.depth = 0)
    {η E : ℝ} (hη : 0 ≤ η) (hE : 0 ≤ E)
    (offset : ∀ q ∈ interior d, |v (lag d q)| ≤ η)
    (spring : ∀ q ∈ interior d, cap d q ≤ E)
    (t : d.Tags) (V : Config G c) (x : Descent.Fields G d) :
    |d.account v t V x| ≤ (d.depth * (n.val^4 * 4) : ℕ) * (η*E) := by
  rw [middle d v top]
  calc
    _ ≤ ∑ q ∈ interior d, |v (lag d q) * cell G d t V x q| := abs_sum_le_sum_abs ..
    _ ≤ ∑ _q ∈ interior d, η*E := sum_le_sum fun q hq => by
      obtain ⟨lo,hi⟩ := bounded d t V x q
      rw [abs_mul, abs_of_nonneg lo]
      exact mul_le_mul (offset q hq) (hi.trans (spring q hq)) lo hη
    _ = ((interior d).card : ℝ) * (η*E) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast count_interior d) (mul_nonneg hη hE)

private lemma sandwich (d : Descent n c) (h : d.OK G) (β v : ℕ → ℝ)
    (V : Config G c) {f : Config G n → ℝ} (hf : Continuous f) (fp : ∀ U, 0 ≤ f U)
    (K : ℝ) (bound : ∀ t x, |d.account v t V x| ≤ K) :
    Real.exp (-K) * mass d β f V ≤ mass d (line β v 1) f V ∧
    mass d (line β v 1) f V ≤ Real.exp K * mass d β f V := by
  have pos (t : d.Tags) (x : Descent.Fields G d) : 0 ≤ d.integrand β t f V x :=
    mul_nonneg (mul_nonneg (d.probability_nonneg ..) (Real.exp_pos _).le) (fp _)
  have reweight (t : d.Tags) (x : Descent.Fields G d) :
      d.integrand (line β v 1) t f V x = Real.exp (-d.account v t V x) * d.integrand β t f V x := by
    simp only [Descent.integrand, WilsonUniformUnmarkedInletSignedResponse.account, one_mul,
      neg_add, Real.exp_add]
    ring
  unfold mass
  rw [mul_sum, mul_sum]
  constructor
  · apply sum_le_sum
    intro t _
    rw [← integral_const_mul]
    apply integral_mono ((d.path_integrable h β t f hf V).const_mul _) (d.path_integrable h _ t f hf V)
    intro x
    rw [reweight]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (le_of_abs_le (bound ..)))) (pos ..)
  · apply sum_le_sum
    intro t _
    rw [← integral_const_mul]
    apply integral_mono (d.path_integrable h _ t f hf V) ((d.path_integrable h β t f hf V).const_mul _)
    intro x
    rw [reweight]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le.mpr (abs_le.mp (bound t x)).1)) (pos ..)

/-- A log partition difference divided by the terminal volume. The only size
factor is the fine/terminal site-count ratio times the traversal length. -/
theorem pressure_step {A : Levels G} {p N k : ℕ} (T : Slices A p) (hk : k ≤ N)
    (β v : ℕ → ℝ) (top : v (traversal T hk).depth = 0)
    {η : ℝ} (hη : 0 ≤ η) (offset : ∀ j, 0 < j → j < (traversal T hk).depth → |v j| ≤ η)
    (V : Config G (A.S.side k p)) {f : Config G (A.S.side N p) → ℝ}
    (hf : Continuous f) (fp : ∀ U, 0 ≤ f U) (hm : 0 < mass (traversal T hk) β f V) :
    let d := traversal T hk
    let vol : ℝ := Fintype.card (Site (A.S.side k p))
    |Real.log (mass d (line β v 1) f V) - Real.log (mass d β f V)| / vol ≤
      ((d.depth * ((A.S.side N p).val^4 * 4) : ℕ) / vol) * (η * (A.clock.kernel.penalty * 2)) := by
  intro d vol
  let K : ℝ := (d.depth * ((A.S.side N p).val^4 * 4) : ℕ) * (η * (A.clock.kernel.penalty * 2))
  have posV : 0 ≤ vol := by dsimp [vol]; positivity
  have hscore (t : d.Tags) (x : Descent.Fields G d) : |d.account v t V x| ≤ K := by
    apply score_cap d v top hη (mul_nonneg A.clock.kernel.penalty_pos.le zero_le_two)
    · exact fun q hq => offset _ (mem_filter.mp hq).2.1 (mem_filter.mp hq).2.2
    · exact fun q hq => (interior_cap T hk q (mem_filter.mp hq).2.2).le
  obtain ⟨lo,hi⟩ := sandwich d (traversal_ok T hk) β v V hf fp K hscore
  have hm' : 0 < mass d (line β v 1) f V := (mul_pos (Real.exp_pos _) hm).trans_le lo
  have a := Real.log_le_log (mul_pos (Real.exp_pos _) hm) lo
  have b := Real.log_le_log hm' hi
  rw [Real.log_mul (Real.exp_pos _).ne' hm.ne', Real.log_exp] at a b
  have bill : |Real.log (mass d (line β v 1) f V) - Real.log (mass d β f V)| ≤ K :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  exact (div_le_div_of_nonneg_right bill posV).trans_eq (by dsimp [K]; ring)

end YM.Integration.InletSusceptibility
