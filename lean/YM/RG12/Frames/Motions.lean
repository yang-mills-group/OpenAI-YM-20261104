import YM.RG12.Frames.Payment

/-!
# March the measuring labels using only ratio measurements along the march

`Moves` consumes normalized prices between *adjacent* frames. `settle` (later file)
exports bounds against a fixed-reference filtration, restoring exact engineering and retaining
only polynomial loss in positive log age. Calendar fit hypotheses are exposed; the dilation
step can be anything ≥ 1 (even use varying mesh!). Do not use a nonconvergence estimate with a
constant correction to the step, or one tending ineffectively to zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Frames
open Function Finset Filter
open scoped Topology BigOperators
variable {d : ℕ} {V : Grade d → Type} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]

def trimBelow (w : Grade d) (x : Col V) : Col V := fun i => if w ≤ i then x i else 0

/-- Period-independent length *units*. In the dyadic march this is constant. Acts on
pivot-input labels, not on the quotient until calibrated. -/
def dilate (s : ℝ) : BlockMatrix V where
  toFun x i := ((s ^ i.val : ℝ) : ℂ) • x i
  map_add' _ _ := by ext1; simp only [Pi.add_apply, smul_add]
  map_smul' c _ := by ext i; simp only [RingHom.id_apply, Pi.smul_apply]; exact smul_comm ..

lemma dilation (s : ℝ) (x : Col V) (i : Grade d) : dilate s x i = ((s^i.val:ℝ):ℂ) • x i := rfl
lemma scale_cancel {s : ℝ} (hs : s ≠ 0) (x : Col V) : dilate s⁻¹ (dilate s x) = x := by
  funext i
  rw [dilation,dilation, smul_smul,← Complex.ofReal_mul, inv_pow,inv_mul_cancel₀ (pow_ne_zero _ hs), Complex.ofReal_one, one_smul]
lemma scale_cancel' {s : ℝ} (hs : s ≠ 0) (x : Col V) : dilate s (dilate s⁻¹ x) = x := by simpa using scale_cancel (s:=s⁻¹) (inv_ne_zero hs) x
lemma tri_dilate (s : ℝ) : triangular V (dilate s) := by
  intro i j hij x; change ((s^ i.val:ℝ):ℂ) • Pi.single j x i = 0
  rw [Pi.single_eq_of_ne (ne_of_gt hij),smul_zero]
lemma coins_trim {b : ℕ} {g : Currency V} {K s : ℝ} (h : Fits g K) (hs : 0 ≤ s) (w : Grade d) (x : Col V) :
    coins b g s (trimBelow w x) ≤ coins b g s x := by
  refine sum_le_sum (s:=univ) fun i _ => ?_
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs _)
  unfold trimBelow; split
  · exact le_rfl
  rw [h.zero]; exact h.nonneg ..

lemma trim_redundant {A : BlockMatrix V} (ha : triangular V A) (w : Grade d) (x : Col V) :
    trimBelow w (A x) = trimBelow w (A (trimBelow w x)) := by
  funext i; dsimp only [trimBelow]; split
  · next he =>
    rw [block_sum,block_sum]; apply sum_congr rfl; intro j _; unfold trimBelow; split
    · exact rfl
    next h => rw [zero_block]; exact ha i j ((lt_of_not_ge h).trans_le he) (x j)
  rfl
lemma trim_dilate (s : ℝ) (w : Grade d) (x : Col V) :
    trimBelow w (dilate s x) = dilate s (trimBelow w x) := by
  funext i; unfold trimBelow; rw [dilation,dilation]; split; rfl; exact (smul_zero _).symm

lemma shrink_price {b : ℕ} {g : Currency V} {K s lambda : ℝ} (h : Fits g K) (hs : 0 ≤ s)
    (hL : 1 ≤ lambda) (w : Grade d) (x : Col V) :
    coins b g s (dilate lambda⁻¹ (trimBelow w x)) ≤ lambda⁻¹^w.val * coins b g s (trimBelow w x) := by
  have hl := zero_lt_one.trans_le hL; have hp := inv_pos.mpr hl
  unfold coins; rw [mul_sum]; apply sum_le_sum; intro i _
  rw [dilation, h.real_scale _ _ (pow_nonneg hp.le _), ← mul_left_comm]
  unfold trimBelow; split
  · next he =>
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hp.le (inv_le_one_of_one_le₀ hL) he)
        (mul_nonneg (pow_nonneg hs _) (h.nonneg ..))
  simp only [h.zero,mul_zero, le_refl]

lemma grow_price {b : ℕ} {g : Currency V} {K s lambda : ℝ} (h : Fits g K) (hs : 0 ≤ s)
    (hL : 1 ≤ lambda) {w : Grade d} {x : Col V} (hx : x ∈ flag V w) :
    coins b g s (dilate lambda x) ≤ lambda^w.val * coins b g s x := by
  unfold coins; rw [mul_sum]; apply sum_le_sum; intro i _
  rw [dilation, h.real_scale _ _ (pow_nonneg (zero_le_one.trans hL) _), ← mul_left_comm]
  by_cases he : i ≤ w
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL he) (mul_nonneg (pow_nonneg hs _) (h.nonneg ..))
  rw [hx i (lt_of_not_ge he), h.zero i]; simp only [mul_zero,le_refl]

variable {F : Type} [AddCommGroup F] [Module ℂ F]
/-- Test prices need only apply starting at n₀, which can be extremely late depending on
the finite demand; the *costs* must refer to arbitrary future scales. Y takes all normalized
(non-redundant) moving labels into this ONE physical space. `low` refers to the whole
compatible filtration already specified on the physical quotient: we can use any reference
splitting `P`, pricing steps only on the grade blocks. -/
structure Moves (s length ratio : ℕ → ℝ) (Y : ℕ → Col V ≃ₗ[ℂ] F) (P : Col V ≃ₗ[ℂ] F)
    (forward : ℕ → Col V ≃ₗ[ℂ] Col V) (g : ℕ → Currency V)
    (K : ℝ) (p b n₀ : ℕ) : Prop where
  spacing (i : ℕ) (he : n₀ ≤ i) : 0 < length i ∧ 1 ≤ ratio i ∧ length (i+1) = length i / ratio i
  clock (i : ℕ) (he : n₀ ≤ i) : 1 ≤ s i ∧ s i + 1 ≤ s (i+1)
  forward_step (i : ℕ) (he : n₀ ≤ i) : Step (forward i).toLinearMap (g i) (g (i+1)) K (s i)
    (s (i+1) / s i) p b
  return_step (i : ℕ) (he : n₀ ≤ i) : Step (forward i).symm.toLinearMap (g (i+1)) (g i) K (s i)
    (s (i+1)/s i) p b
  realized (i : ℕ) (he : n₀ ≤ i) (x : Col V) : Y (i+1) x = Y i (forward i (dilate (ratio i)⁻¹ x))
  low : triangular V ((Y n₀).trans P.symm).toLinearMap

variable {s t u : ℕ → ℝ} {Y : ℕ → Col V ≃ₗ[ℂ] F} {P : Col V ≃ₗ[ℂ] F}
  {A : ℕ → Col V ≃ₗ[ℂ] Col V} {g : ℕ → Currency V} {K : ℝ} {p b n₀ : ℕ}

lemma Moves.clock_ratio (h : Moves s t u Y P A g K p b n₀) (i : ℕ) (he : n₀ ≤ i) :
    1+(s i)⁻¹ ≤ s (i+1) / s i := by
  obtain ⟨h₁,h₂⟩ := h.clock i he; rw [le_div_iff₀ (zero_lt_one.trans_le h₁), add_mul, one_mul, inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le h₁))]; exact h₂

lemma Moves.unit_ratio (h : Moves s t u Y P A g K p b n₀) (i : ℕ) (he : n₀ ≤ i) :
    1 ≤ s (i+1) / s i := (one_le_div (zero_lt_one.trans_le (h.clock i he).1)).2 ((le_add_of_nonneg_right zero_le_one).trans (h.clock i he).2)

lemma Moves.backward (h : Moves s t u Y P A g K p b n₀) (i : ℕ) (he : n₀ ≤ i) (x : F) :
    (Y (i+1)).symm x = dilate (u i) ((A i).symm ((Y i).symm x)) := by
  apply (Y (i+1)).injective
  rw [LinearEquiv.apply_symm_apply, h.realized i he, scale_cancel (ne_of_gt (zero_lt_one.trans_le (h.spacing i he).2.1)),LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

lemma Moves.always (h : Moves s t u Y P A g K p b n₀) (i : ℕ) (he : n₀ ≤ i) :
    triangular V ((Y i).trans P.symm).toLinearMap := by
  induction he with
  | refl=> exact h.low
  | @step i he ih=>
    have ht := (ih.comp (h.forward_step i he).stays).comp (tri_dilate (V:=V) (u i)⁻¹)
    intro j l hL x; change P.symm (Y (i+1) _) j = _; rw [h.realized i he]
    exact ht j l hL x
end YM.RG12.Frames
