import YM.Push.STATIONARY_UNIFORM.Entries

/-! Fixed-order scalar bounds for the literal joint-payload tariff.
The finite rank sum is the defining expression of NativeJointPayloadTensor.rankPrice.
The coefficient and degree precede the side and width.  No PaintSupply, Run,
or analytic receipt is assumed; absolute values retain arbitrary fixed Z. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.UniformJointPricePolynomial

open Lattice Wilson RG Precision Tree Pressure Gauge Exterior
open Next.Fluctuations Push.Uniform
open scoped BigOperators

private structure Trial where
  L : Side
  μ : ℝ

private structure Admissible (x : Trial) : Prop where
  width_pos : 0 < x.μ
  width_cap : x.μ ≤ 1

private def base (x : Trial) : ℝ := 1 + (x.L.val : ℝ) + x.μ⁻¹

private lemma base_bounds (x : Trial) (h : Admissible x) :
    1 ≤ base x ∧ (x.L.val : ℝ) ≤ base x ∧ x.μ⁻¹ ≤ base x := by
  have hL : 0 ≤ (x.L.val : ℝ) := Nat.cast_nonneg _
  have hμ := (inv_pos.mpr h.width_pos).le
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [base] <;> linarith

private lemma base_nonneg (x : Trial) (h : Admissible x) : 0 ≤ base x :=
  zero_le_one.trans (base_bounds x h).1

private lemma width_le_one (x : Trial) (h : Admissible x) : x.μ ≤ 1 :=
  h.width_cap

/-- The witnesses depend only on the function's fixed parameters. -/
private def PolyBound (f : Trial → ℝ) : Prop :=
  ∃ d : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ x, Admissible x → |f x| ≤ A * base x ^ d

private lemma poly_const (a : ℝ) : PolyBound (fun _ => a) := by
  refine ⟨0, 1 + |a|, by positivity, fun x h => ?_⟩
  simp only [pow_zero, mul_one]
  linarith

private lemma PolyBound.add {f g : Trial → ℝ}
    (hf : PolyBound f) (hg : PolyBound g) : PolyBound (fun x => f x + g x) := by
  obtain ⟨p, C, hC, hf⟩ := hf
  obtain ⟨q, D, hD, hg⟩ := hg
  refine ⟨max p q, C + D, by positivity, fun x hx => ?_⟩
  have ht := (base_bounds x hx).1
  apply le_trans ((abs_add_le ..).trans (add_le_add (hf x hx) (hg x hx)))
  rw [add_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_left ..)) hC.le)
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (le_max_right ..)) hD.le)

private lemma PolyBound.mul {f g : Trial → ℝ}
    (hf : PolyBound f) (hg : PolyBound g) : PolyBound (fun x => f x * g x) := by
  obtain ⟨p, C, hC, hf⟩ := hf
  obtain ⟨q, D, hD, hg⟩ := hg
  refine ⟨p + q, C * D, by positivity, fun x hx => ?_⟩
  have hb := base_nonneg x hx
  rw [abs_mul]
  apply (mul_le_mul (hf x hx) (hg x hx) (abs_nonneg _) (by positivity)).trans_eq
  rw [pow_add]
  ring

private lemma PolyBound.ltMore {f g : Trial → ℝ} (hf : PolyBound f)
    (he : ∀ x, Admissible x → |g x| ≤ f x) : PolyBound g := by
  obtain ⟨p, C, hC, hf⟩ := hf
  exact ⟨p, C, hC, fun x hx => (he x hx).trans ((le_abs_self _).trans (hf x hx))⟩

private lemma PolyBound.at_eq {f g : Trial → ℝ} (hf : PolyBound f)
    (he : ∀ x, Admissible x → f x = g x) : PolyBound g := by
  obtain ⟨p, C, hC, hf⟩ := hf
  exact ⟨p, C, hC, fun x hx => by rw [← he x hx]; exact hf x hx⟩

private lemma PolyBound.absolute {f : Trial → ℝ} (hf : PolyBound f) :
    PolyBound (fun x => |f x|) := by
  obtain ⟨p, C, hC, hf⟩ := hf
  exact ⟨p, C, hC, fun x hx => by simpa only [abs_abs] using hf x hx⟩

private lemma PolyBound.power {f : Trial → ℝ} (hf : PolyBound f) (k : ℕ) :
    PolyBound (fun x => f x ^ k) := by
  induction k with
  | zero => simp_rw [pow_zero]; exact poly_const _
  | succ k ih => simp_rw [pow_succ]; exact ih.mul hf

private lemma PolyBound.exp' {f : Trial → ℝ} {A : ℝ}
    (h : ∀ x, Admissible x → f x ≤ A) : PolyBound (fun x => Real.exp (f x)) := by
  apply (poly_const (Real.exp A)).ltMore
  intro x hx
  rw [abs_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_monotone (h x hx)

private lemma poly_of_le_base {f : Trial → ℝ}
    (h : ∀ x, Admissible x → |f x| ≤ base x) : PolyBound f := by
  refine ⟨1, 1, zero_lt_one, fun x hx => ?_⟩
  simpa only [pow_one, one_mul] using h x hx

private lemma poly_L : PolyBound (fun x => (x.L.val : ℝ)) := by
  apply poly_of_le_base
  intro x h
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact (base_bounds x h).2.1

private lemma poly_inverse_width : PolyBound (fun x => x.μ⁻¹) := by
  apply poly_of_le_base
  intro x h
  rw [abs_of_pos (inv_pos.mpr h.width_pos)]
  exact (base_bounds x h).2.2

private lemma poly_compose {f g : Trial → ℝ}
    (hf : PolyBound f) (hg : PolyBound g) (n : ℕ) :
    PolyBound (fun x => composeCost n (f x) (g x)) :=
  ((poly_const _).mul hf).mul (((poly_const 1).add hg).power n)


private lemma poly_small_radius_inverse :
    PolyBound (fun x => (Work.F02.radius (x.μ / 2))⁻¹) := by
  apply ((poly_const 4).mul poly_inverse_width).ltMore
  intro x h
  have hp := Work.F02.radius_pos (half_pos h.width_pos)
  have hlow : x.μ / 4 ≤ Work.F02.radius (x.μ / 2) := by
    have he := Real.add_one_le_exp ((x.μ / 2) / 2)
    dsimp [Work.F02.radius]
    linarith
  rw [abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (x.μ / 4)⁻¹ := inv_anti₀ (div_pos h.width_pos (by norm_num)) hlow
    _ = 4 * x.μ⁻¹ := by
      simp only [div_eq_mul_inv, _root_.mul_inv, inv_inv]
      ring

private lemma poly_path (G : Gauge) (n : ℕ) (Z : ℝ) :
    PolyBound (fun x => pathPrice G Z x.μ n) := by
  have hf := ((poly_const 1).add
    ((poly_const ((2 : ℝ)^n)).mul poly_small_radius_inverse)).power n
  simpa only [pathPrice, div_eq_mul_inv] using
    poly_compose hf (poly_const (fineCost G n Z)) n

private lemma poly_exp_width : PolyBound (fun x => Real.exp x.μ) :=
  PolyBound.exp' (fun x h => width_le_one x h)


private lemma poly_atom (G : Gauge) (n k : ℕ) (Z : ℝ) :
    PolyBound (fun x => atomCost G Z x.μ n k) :=
  ((poly_path G n Z).mul (poly_const _)).mul poly_exp_width


private lemma entry_le_width (x : Trial) (h : Admissible x) (n : ℕ) :
    entryWidth n x.L x.μ ≤ x.μ := by
  unfold entryWidth
  apply div_le_self h.width_pos.le
  calc
    (1 : ℝ) ≤ 4 * (1 : ℝ) * 1 := by norm_num
    _ ≤ 4 * ((n : ℝ) + 1) * (1 + (x.L.val : ℝ)) := by
      gcongr
      · exact le_add_of_nonneg_left (Nat.cast_nonneg n)
      · exact le_add_of_nonneg_right (Nat.cast_nonneg x.L.val)


private lemma poly_entry_inverse (n : ℕ) :
    PolyBound (fun x => (entryWidth n x.L x.μ / 2)⁻¹) := by
  apply ((((poly_const 8).mul (poly_const ((n : ℝ) + 1))).mul
    ((poly_const 1).add poly_L)).mul poly_inverse_width).at_eq
  intro x _
  simp only [entryWidth, div_eq_mul_inv, _root_.mul_inv, inv_inv]
  ring

private lemma poly_count (n : ℕ) :
    PolyBound (fun x => countCost (entryWidth n x.L x.μ / 2)) := by
  have he : PolyBound (fun x : Trial =>
      Real.exp ((entryWidth n x.L x.μ / 2) * 2)) := by
    apply PolyBound.exp' (A := 1)
    intro x h
    have hw := (entry_le_width x h n).trans (width_le_one x h)
    linarith
  simpa only [countCost, div_eq_mul_inv, ← inv_pow] using
    ((he.mul (poly_const (Nat.factorial 6 : ℝ))).mul
      ((poly_entry_inverse n).power 6)).mul (poly_const ((2 : ℝ)^4))


private lemma poly_weaker_inverse (n : ℕ) :
    PolyBound (fun x => (weaker n (entryWidth n x.L x.μ))⁻¹) := by
  apply ((poly_const ((n : ℝ) + 1)).mul (poly_entry_inverse n)).at_eq
  intro x _
  simp only [weaker, entryWidth, div_eq_mul_inv, _root_.mul_inv, inv_inv]
  ring

private lemma poly_weaker_count (n : ℕ) :
    PolyBound (fun x => countCost (weaker n (entryWidth n x.L x.μ))) := by
  have he : PolyBound (fun x : Trial =>
      Real.exp (weaker n (entryWidth n x.L x.μ) * 2)) := by
    apply PolyBound.exp' (A := 1)
    intro x h
    have hw := (entry_le_width x h n).trans h.width_cap
    unfold weaker
    rw [div_mul_eq_mul_div, div_le_iff₀
      (show 0 < 2 * ((n : ℝ) + 1) by positivity)]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  simpa only [countCost, div_eq_mul_inv, ← inv_pow] using
    ((he.mul (poly_const (Nat.factorial 6 : ℝ))).mul
      ((poly_weaker_inverse n).power 6)).mul (poly_const ((2 : ℝ)^4))

private lemma poly_rank (G : Gauge) (N cap : ℕ) (Z : ℝ) :
    PolyBound (fun x => ∑ k ∈ Finset.range (cap + 1), atomCost G Z x.μ N k) := by
  have hh (m : ℕ) :
      PolyBound (fun x => ∑ k ∈ Finset.range m, atomCost G Z x.μ N k) := by
    induction m with
    | zero => simpa only [Finset.range_zero, Finset.sum_empty] using (poly_const 0)
    | succ m ih =>
        simpa only [Finset.sum_range_succ] using ih.add (poly_atom G N m Z)
  exact hh (cap + 1)

/-- One scalar majorant for both the coordinate factor and every degree through N.
The rank sum is literal, so the tensor rankPrice reduces to it by unfolding. -/
def majorant (G : Gauge) (N cap : ℕ) (Z : ℝ) (L : Side) (μ : ℝ) : ℝ :=
  (1 + |(∑ k ∈ Finset.range (cap + 1), atomCost G Z μ N k) *
    countCost (entryWidth N L μ / 2)|) *
  (1 + |(townCost G : ℝ) * countCost (weaker N (entryWidth N L μ))|)^N

private lemma poly_majorant (G : Gauge) (N cap : ℕ) (Z : ℝ) :
    PolyBound (fun x => majorant G N cap Z x.L x.μ) := by
  have hA := (poly_rank G N cap Z).mul (poly_count N)
  have hD := (poly_const (townCost G : ℝ)).mul (poly_weaker_count N)
  exact ((poly_const 1).add hA.absolute).mul
    (((poly_const 1).add hD.absolute).power N)

/-- The majorant retains the complete rank sum and the full coordinate factor. -/
theorem domination (G : Gauge) (N cap : ℕ) (Z : ℝ) (L : Side) (μ : ℝ) :
    |(∑ k ∈ Finset.range (cap + 1), atomCost G Z μ N k) *
        countCost (entryWidth N L μ / 2)| ≤ majorant G N cap Z L μ ∧
    ∀ d : ℕ, d ≤ N →
      |((∑ k ∈ Finset.range (cap + 1), atomCost G Z μ N k) *
        countCost (entryWidth N L μ / 2)) *
        ((townCost G : ℝ) * countCost (weaker N (entryWidth N L μ)))^d| ≤
        majorant G N cap Z L μ := by
  let A := (∑ k ∈ Finset.range (cap + 1), atomCost G Z μ N k) *
    countCost (entryWidth N L μ / 2)
  let D := (townCost G : ℝ) * countCost (weaker N (entryWidth N L μ))
  change |A| ≤ (1 + |A|) * (1 + |D|)^N ∧
    ∀ d : ℕ, d ≤ N → |A * D^d| ≤ (1 + |A|) * (1 + |D|)^N
  have hb : 1 ≤ 1 + |D| := by linarith [abs_nonneg D]
  have hp : 1 ≤ (1 + |D|)^N := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hb N)
  constructor
  · calc
      |A| ≤ (1 + |A|) * 1 := by linarith
      _ ≤ (1 + |A|) * (1 + |D|)^N :=
        mul_le_mul_of_nonneg_left hp (by positivity)
  · intro d hd
    rw [abs_mul, abs_pow]
    have hpow : |D|^d ≤ (1 + |D|)^N :=
      (pow_le_pow_left₀ (abs_nonneg D)
        (show |D| ≤ 1 + |D| by linarith) d).trans (pow_le_pow_right₀ hb hd)
    exact mul_le_mul (show |A| ≤ 1 + |A| by linarith) hpow
      (pow_nonneg (abs_nonneg D) d) (by positivity)

/-- Fixed G, N, cap and Z determine one positive coefficient and finite degree. -/
theorem polynomial (G : Gauge) (N cap : ℕ) (Z : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (L : Side) (μ : ℝ),
      0 < μ → μ ≤ 1 →
      majorant G N cap Z L μ ≤ C * (1 + (L.val : ℝ) + μ⁻¹)^k := by
  obtain ⟨k, C, hC, hh⟩ := poly_majorant G N cap Z
  refine ⟨C, hC, k, fun L μ hm hu => ?_⟩
  exact (le_abs_self _).trans (hh ⟨L, μ⟩ ⟨hm, hu⟩)

/-- The same coefficient and degree pay both requested literal scalar factors. -/
theorem bound (G : Gauge) (N cap : ℕ) (Z : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ (L : Side) (μ : ℝ),
      0 < μ → μ ≤ 1 →
      |(∑ j ∈ Finset.range (cap + 1), atomCost G Z μ N j) *
          countCost (entryWidth N L μ / 2)| ≤ C * (1 + (L.val : ℝ) + μ⁻¹)^k ∧
      ∀ d : ℕ, d ≤ N →
        |((∑ j ∈ Finset.range (cap + 1), atomCost G Z μ N j) *
          countCost (entryWidth N L μ / 2)) *
          ((townCost G : ℝ) * countCost (weaker N (entryWidth N L μ)))^d| ≤
          C * (1 + (L.val : ℝ) + μ⁻¹)^k := by
  obtain ⟨C, hC, k, hh⟩ := polynomial G N cap Z
  refine ⟨C, hC, k, fun L μ hm hu => ?_⟩
  have h := domination G N cap Z L μ
  exact ⟨h.1.trans (hh L μ hm hu), fun d hd => (h.2 d hd).trans (hh L μ hm hu)⟩

end YM.Integration.UniformJointPricePolynomial
end
