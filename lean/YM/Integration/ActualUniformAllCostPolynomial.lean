import YM.Push.STATIONARY_UNIFORM.ScoreBounds

/-! A fixed-order polynomial bound for the literal stationary score bill.
The coefficient and degree precede the patch, width, path budget, quadratic
budget and clip.  The width cap pays the displayed patch exponentials; all
inverse widths, path factors and finite implicit-jet recursions remain. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualUniformAllCostPolynomial

open Lattice Wilson RG Precision Tree Pressure Gauge Exterior
open Next.Fluctuations Push.Uniform
open scoped BigOperators

private structure Trial where
  P : Patch
  μ : ℝ
  C : ℝ
  X : ℝ
  p : Clip

private structure Admissible (x : Trial) : Prop where
  cost_nonneg : 0 ≤ x.C
  square_nonneg : 0 ≤ x.X
  width_pos : 0 < x.μ
  width_cap : x.μ * ((x.P.J : ℝ) + 3) ≤ 1

private def base (x : Trial) : ℝ :=
  1 + x.C + x.X + |x.p.direct| + (x.P.L.val : ℝ) + (x.P.J : ℝ) + x.μ⁻¹

private lemma base_bounds (x : Trial) (h : Admissible x) :
    1 ≤ base x ∧ x.C ≤ base x ∧ x.X ≤ base x ∧ |x.p.direct| ≤ base x ∧
    (x.P.L.val : ℝ) ≤ base x ∧ (x.P.J : ℝ) ≤ base x ∧ x.μ⁻¹ ≤ base x := by
  have hC := h.cost_nonneg
  have hX := h.square_nonneg
  have hp := abs_nonneg x.p.direct
  have hL : 0 ≤ (x.P.L.val : ℝ) := Nat.cast_nonneg _
  have hJ : 0 ≤ (x.P.J : ℝ) := Nat.cast_nonneg _
  have hμ := (inv_pos.mpr h.width_pos).le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp [base] <;> linarith

private lemma base_nonneg (x : Trial) (h : Admissible x) : 0 ≤ base x :=
  zero_le_one.trans (base_bounds x h).1

private lemma width_le_one (x : Trial) (h : Admissible x) : x.μ ≤ 1 := by
  have hJ : 0 ≤ x.μ * (x.P.J : ℝ) :=
    mul_nonneg h.width_pos.le (Nat.cast_nonneg _)
  have hc := h.width_cap
  nlinarith [h.width_pos]

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

private lemma poly_C : PolyBound (fun x => x.C) := by
  apply poly_of_le_base
  intro x h
  rw [abs_of_nonneg h.cost_nonneg]
  exact (base_bounds x h).2.1

private lemma poly_X : PolyBound (fun x => x.X) := by
  apply poly_of_le_base
  intro x h
  rw [abs_of_nonneg h.square_nonneg]
  exact (base_bounds x h).2.2.1

private lemma poly_direct : PolyBound (fun x => |x.p.direct|) := by
  apply poly_of_le_base
  intro x h
  rw [abs_abs]
  exact (base_bounds x h).2.2.2.1

private lemma poly_L : PolyBound (fun x => (x.P.L.val : ℝ)) := by
  apply poly_of_le_base
  intro x h
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact (base_bounds x h).2.2.2.2.1

private lemma poly_J : PolyBound (fun x => (x.P.J : ℝ)) := by
  apply poly_of_le_base
  intro x h
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact (base_bounds x h).2.2.2.2.2.1

private lemma poly_inverse_width : PolyBound (fun x => x.μ⁻¹) := by
  apply poly_of_le_base
  intro x h
  rw [abs_of_pos (inv_pos.mpr h.width_pos)]
  exact (base_bounds x h).2.2.2.2.2.2

private lemma poly_radius : PolyBound (fun x => (x.P.radius : ℝ)) := by
  simpa only [Patch.radius, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
    (poly_J.add (poly_const 3)).mul poly_L

private lemma poly_points : PolyBound (fun x => Push.Uniform.points x.P) := by
  apply (((poly_radius.add poly_radius).add (poly_const 1)).power 4).at_eq
  intro x _
  simp only [points_cost, Nat.cast_add, Nat.cast_one]

private lemma poly_gap_inverse : PolyBound (fun x => (rootGap x.P / 2)⁻¹) := by
  apply (poly_points.power 2).at_eq
  intro x _
  have he : rootGap x.P / 2 = (Push.Uniform.points x.P)⁻¹ ^ 2 := by
    unfold rootGap
    ring
  rw [he, ← inv_pow, inv_inv]

private lemma poly_compose {f g : Trial → ℝ}
    (hf : PolyBound f) (hg : PolyBound g) (n : ℕ) :
    PolyBound (fun x => composeCost n (f x) (g x)) :=
  ((poly_const _).mul hf).mul (((poly_const 1).add hg).power n)

private lemma poly_travel (G : Gauge) {u : Trial → ℕ}
    (hu : PolyBound (fun x => (u x : ℝ))) (C : ℝ) (n : ℕ) :
    PolyBound (fun x => travelCost G n (u x) C) :=
  poly_compose
    ((poly_const _).mul
      (((poly_const 1).add ((poly_const _).mul ((poly_const 1).add hu))).power n))
    (poly_const C) n

private lemma poly_price (G : Gauge) {f : Trial → ℝ} (hf : PolyBound f) :
    PolyBound (fun x => priceCost G (f x)) :=
  (poly_const 1).add ((poly_const _).mul hf)

private lemma poly_score (G : Gauge) (n : ℕ) (K C : ℝ) :
    PolyBound (fun x => scoreCost x.P G n K C) := by
  have hu : PolyBound (fun x : Trial => ((8 * x.P.radius : ℕ) : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (poly_const 8).mul poly_radius
  have ht := poly_travel G hu (composeCost n C 1) n
  exact poly_price G
    (((poly_const _).mul (((poly_const _).mul (poly_const _)).mul ht)).mul
      (poly_const _))

private lemma poly_implicit {f g : Trial → ℝ}
    (hf : PolyBound f) (hg : PolyBound g) (n : ℕ) :
    PolyBound (fun x => implicitCost 1 (f x) (g x) n) := by
  induction n with
  | zero => exact poly_const 1
  | succ n ih =>
      exact ih.add
        (hg.mul (hf.add (((poly_const _).mul hf).mul
          (((poly_const 1).add ih).power (n + 1)))))

private lemma poly_connector (G : Gauge) (n : ℕ) (K C : ℝ) :
    PolyBound (fun x => connectorCost x.P G n K C) := by
  have hf : PolyBound (fun x : Trial => hatsCost x.P G n K C) :=
    poly_compose (poly_const K)
      (poly_implicit (poly_score G (n + 1) K C) poly_gap_inverse n) n
  have ht := poly_travel G poly_L C n
  exact ((poly_const _).mul (((poly_const _).mul hf).mul ht)).mul hf

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

private lemma poly_roots (G : Gauge) (n : ℕ) (Z : ℝ) :
    PolyBound (fun x => rootsCost G Z x.μ n) :=
  (((poly_path G n Z).mul (poly_const _)).mul (poly_const _)).mul poly_exp_width

private lemma poly_atom (G : Gauge) (n k : ℕ) (Z : ℝ) :
    PolyBound (fun x => atomCost G Z x.μ n k) :=
  ((poly_path G n Z).mul (poly_const _)).mul poly_exp_width

private lemma entry_le_width (x : Trial) (h : Admissible x) (n : ℕ) :
    entryWidth n x.P.L x.μ ≤ x.μ := by
  unfold entryWidth
  apply div_le_self h.width_pos.le
  calc
    (1 : ℝ) ≤ 4 * (1 : ℝ) * 1 := by norm_num
    _ ≤ 4 * ((n : ℝ) + 1) * (1 + (x.P.L.val : ℝ)) := by
      gcongr
      · exact le_add_of_nonneg_left (Nat.cast_nonneg n)
      · exact le_add_of_nonneg_right (Nat.cast_nonneg x.P.L.val)

private lemma entry_times_L (x : Trial) (h : Admissible x) (n : ℕ) :
    entryWidth n x.P.L x.μ * x.P.L.val ≤ x.μ := by
  unfold entryWidth
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity :
    0 < 4 * ((n : ℝ) + 1) * (1 + (x.P.L.val : ℝ)))]
  apply mul_le_mul_of_nonneg_left _ h.width_pos.le
  have hnL : 0 ≤ (n : ℝ) * (x.P.L.val : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hL : 0 ≤ (x.P.L.val : ℝ) := Nat.cast_nonneg _
  linarith

private lemma poly_entry_inverse (n : ℕ) :
    PolyBound (fun x => (entryWidth n x.P.L x.μ / 2)⁻¹) := by
  apply ((((poly_const 8).mul (poly_const ((n : ℝ) + 1))).mul
    ((poly_const 1).add poly_L)).mul poly_inverse_width).at_eq
  intro x _
  simp only [entryWidth, div_eq_mul_inv, _root_.mul_inv, inv_inv]
  ring

private lemma poly_count (n : ℕ) :
    PolyBound (fun x => countCost (entryWidth n x.P.L x.μ / 2)) := by
  have he : PolyBound (fun x : Trial =>
      Real.exp ((entryWidth n x.P.L x.μ / 2) * 2)) := by
    apply PolyBound.exp' (A := 1)
    intro x h
    have hw := (entry_le_width x h n).trans (width_le_one x h)
    linarith
  simpa only [countCost, div_eq_mul_inv, ← inv_pow] using
    ((he.mul (poly_const (Nat.factorial 6 : ℝ))).mul
      ((poly_entry_inverse n).power 6)).mul (poly_const ((2 : ℝ)^4))

private lemma quad_exponent_le (x : Trial) (h : Admissible x) (n : ℕ) :
    entryWidth n x.P.L x.μ * ((n * signedCost x.P.L 4 : ℕ) : ℝ) ≤
      x.μ * (n : ℝ) * (5 + 1) := by
  unfold entryWidth signedCost
  push_cast
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity :
    0 < 4 * ((n : ℝ) + 1) * (1 + (x.P.L.val : ℝ)))]
  apply le_trans (mul_le_mul_of_nonneg_left
    (show (n : ℝ) * (5 + (x.P.L.val : ℝ)) ≤
      n * (5 + 1) * (4 * ((n : ℝ) + 1) * (1 + (x.P.L.val : ℝ))) from ?_)
    h.width_pos.le)
  · exact le_of_eq (by ring)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hL : 0 ≤ (x.P.L.val : ℝ) := Nat.cast_nonneg _
  have hnL : 0 ≤ (n : ℝ) * (x.P.L.val : ℝ) := by positivity
  have hnnL : 0 ≤ (n : ℝ) * n * (x.P.L.val : ℝ) := by positivity
  nlinarith

private lemma poly_quad_exp (n : ℕ) : PolyBound (fun x =>
    Real.exp (entryWidth n x.P.L x.μ * ((n * signedCost x.P.L 4 : ℕ) : ℝ))) := by
  apply PolyBound.exp' (A := (n : ℝ) * (5 + 1))
  intro x h
  apply (quad_exponent_le x h n).trans
  have he := mul_le_mul_of_nonneg_right (width_le_one x h)
    (show 0 ≤ (n : ℝ) * (5 + 1) by positivity)
  simpa only [one_mul, mul_assoc] using he

private lemma noise_exponent_le (x : Trial) (h : Admissible x) (n : ℕ) :
    entryWidth n x.P.L x.μ * ((n * noiseCost x.P : ℕ) : ℝ) ≤ 19 * (n : ℝ) := by
  let a : ℝ := 1 + 16 * ((x.P.J : ℝ) + 3) + 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : (noiseCost x.P : ℝ) = (x.P.L.val : ℝ) * a := by
    unfold noiseCost Patch.radius a
    push_cast
    ring
  have hμ := width_le_one x h
  have hcap := h.width_cap
  have hcost : x.μ * a ≤ 19 := by dsimp [a]; nlinarith
  calc
    _ = (entryWidth n x.P.L x.μ * x.P.L.val) * ((n : ℝ) * a) := by
      rw [Nat.cast_mul, he]
      ring
    _ ≤ x.μ * ((n : ℝ) * a) :=
      mul_le_mul_of_nonneg_right (entry_times_L x h n)
        (mul_nonneg (Nat.cast_nonneg _) ha)
    _ = (n : ℝ) * (x.μ * a) := by ring
    _ ≤ (n : ℝ) * 19 :=
      mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg _)
    _ = 19 * (n : ℝ) := by ring

private lemma poly_noise_exp (n : ℕ) : PolyBound (fun x =>
    Real.exp (entryWidth n x.P.L x.μ * ((n * noiseCost x.P : ℕ) : ℝ))) :=
  PolyBound.exp' (fun x h => noise_exponent_le x h n)

private lemma poly_quad (G : Gauge) (n : ℕ) (Z : ℝ) :
    PolyBound (fun x => quadCost G n Z x.X x.μ x.C x.p x.P.L) :=
  ((poly_direct.mul (poly_const _)).mul (poly_quad_exp n)).add
    ((poly_const _).mul
      (poly_X.mul (((poly_const 1).add (poly_C.mul (poly_roots G n Z))).power n)))

private lemma poly_main (G : Gauge) (n : ℕ) (Z : ℝ) :
    PolyBound (fun x => mainCost G n Z x.X x.μ x.C x.p x.P.L) :=
  ((((poly_const _).mul (poly_quad G n Z)).add
    (poly_C.mul (poly_atom G n 3 Z))).add
    (poly_C.mul (poly_atom G n 4 Z))).mul (poly_count n)

private lemma poly_noise (G : Gauge) (n : ℕ) (Z K W : ℝ) :
    PolyBound (fun x => noiseEntry G n Z K W x.μ x.P) :=
  (poly_price G ((poly_const _).mul
    (poly_compose (poly_const W)
      (poly_connector G n K (fineCost G (n + 1) Z)) n))).mul (poly_noise_exp n)

private lemma poly_all (G : Gauge) (n : ℕ) (Z K W : ℝ) (Q : KernelChoices) :
    PolyBound (fun x => allCost G n Z x.X x.μ x.C K W x.p x.P Q) :=
  (poly_const 1).add
    (((poly_main G n Z).add ((poly_const |Q.penalty|).mul
      (((poly_noise G n Z K W).mul (poly_const _)).mul (poly_count n)))).absolute)

/-- A companion bound for the original roots bill, with no quadratic budget in
the majorant. This allows the explicit native SquarePay polynomial to be
substituted later without a compactness-selected constant. -/
theorem rootsCost_polynomial (G : Gauge) (n : ℕ) (Z : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∃ d : ℕ,
      ∀ (P : Patch) (μ C : ℝ) (p : Clip),
        0 ≤ C → 0 < μ → μ * ((P.J : ℝ) + 3) ≤ 1 →
        |rootsCost G Z μ n| ≤
          A * (1 + C + |p.direct| + (P.L.val : ℝ) + (P.J : ℝ) + μ⁻¹)^d := by
  obtain ⟨d, A, hA, hbound⟩ := poly_roots G n Z
  refine ⟨A, hA, d, ?_⟩
  intro P μ C p hC hμ hcap
  let x : Trial := ⟨P, μ, C, 0, p⟩
  have hx : Admissible x := ⟨hC, le_rfl, hμ, hcap⟩
  simpa only [base, x, add_zero] using hbound x hx

/-- The complete original bill has a polynomial majorant uniform in the patch
and every displayed variable budget.  Fixed analytic constants may be any
reals; their original positive-receipt specialization adds no new premise. -/
theorem allCost_polynomial (G : Gauge) (n : ℕ) (Z K W : ℝ) (Q : KernelChoices) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ d : ℕ,
      ∀ (P : Patch) (μ C Z' : ℝ) (p : Clip),
        0 ≤ C → 0 ≤ Z' → 0 < μ → μ * ((P.J : ℝ) + 3) ≤ 1 →
        allCost G n Z Z' μ C K W p P Q ≤
          C₀ * (1 + C + Z' + |p.direct| + (P.L.val : ℝ) + (P.J : ℝ) + μ⁻¹)^d := by
  obtain ⟨d, C₀, hC₀, hbound⟩ := poly_all G n Z K W Q
  refine ⟨C₀, hC₀, d, ?_⟩
  intro P μ C Z' p hC hZ hμ hcap
  let x : Trial := ⟨P, μ, C, Z', p⟩
  have hx : Admissible x := ⟨hC, hZ, hμ, hcap⟩
  exact (le_abs_self _).trans (hbound x hx)

end YM.Integration.ActualUniformAllCostPolynomial
end


noncomputable section
namespace YM.Integration.ActualUniformAllCostPolynomial
open Lattice Wilson RG Precision Tree Pressure Gauge Exterior
open Next.Fluctuations Push.Uniform

/-- The literal polynomial SquarePay price can be substituted into the complete
bill before the patch, width, path budget and clip are chosen. -/
theorem allCost_square_polynomial
    (G : Gauge) (n : ℕ) (Z K W : ℝ) (Q : KernelChoices) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ d : ℕ,
      ∀ (P : Patch) (μ C : ℝ) (p : Clip),
        0 ≤ C → 0 < μ → μ * ((P.J : ℝ) + 3) ≤ 1 →
        allCost G n Z
          ((2 : ℝ)^n * (1 + (C * rootsCost G Z μ n)^2))
          μ C K W p P Q ≤
        C₀ * (1 + C + |p.direct| + (P.L.val : ℝ) + (P.J : ℝ) + μ⁻¹)^d := by
  obtain ⟨A, hA, e, hroots⟩ := rootsCost_polynomial G n Z
  obtain ⟨C₀, hC₀, d, hall⟩ := allCost_polynomial G n Z K W Q
  let D : ℝ := 1 + (2 : ℝ)^n * (1 + A^2)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨C₀ * D^d, mul_pos hC₀ (pow_pos hD _), d * (2*e+2), ?_⟩
  intro P μ C p hC hμ hcap
  let B : ℝ := 1 + C + |p.direct| + (P.L.val : ℝ) + (P.J : ℝ) + μ⁻¹
  let X : ℝ := (2 : ℝ)^n * (1 + (C * rootsCost G Z μ n)^2)
  have hL : 0 ≤ (P.L.val : ℝ) := Nat.cast_nonneg _
  have hJ : 0 ≤ (P.J : ℝ) := Nat.cast_nonneg _
  have hi : 0 ≤ μ⁻¹ := (inv_pos.mpr hμ).le
  have hB : 1 ≤ B := by dsimp [B]; linarith [abs_nonneg p.direct]
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hCB : C ≤ B := by dsimp [B]; linarith [abs_nonneg p.direct]
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hr : |rootsCost G Z μ n| ≤ A * B^e := hroots P μ C p hC hμ hcap
  have hm : |C * rootsCost G Z μ n| ≤ B * (A * B^e) := by
    rw [abs_mul, abs_of_nonneg hC]
    exact mul_le_mul hCB hr (abs_nonneg _) hB₀
  have hpowers : B^(2*e+2) = (B^e)^2 * B^2 := by
    rw [show 2*e+2 = e*2+2 by omega, pow_add, pow_mul]
  have hs : (C * rootsCost G Z μ n)^2 ≤ A^2 * B^(2*e+2) := by
    calc
      _ ≤ (B * (A * B^e))^2 := by
        simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) hm 2)
      _ = _ := by rw [hpowers]; ring
  have hP : 1 ≤ B^(2*e+2) := by
    simpa only [pow_zero] using
      (pow_le_pow_right₀ hB (Nat.zero_le (2*e+2)))
  have hBP : B ≤ B^(2*e+2) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ hB (show 1 ≤ 2*e+2 by omega))
  have hXP : X ≤ (2 : ℝ)^n * (1 + A^2) * B^(2*e+2) := by
    dsimp [X]
    calc
      _ ≤ (2 : ℝ)^n * (1 + A^2 * B^(2*e+2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hs) (by positivity)
      _ ≤ (2 : ℝ)^n * (B^(2*e+2) + A^2 * B^(2*e+2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hP (le_refl (A^2 * B^(2*e+2)))) (by positivity)
      _ = _ := by ring
  have hsum : B + X ≤ D * B^(2*e+2) := by
    calc
      _ ≤ B^(2*e+2) + (2 : ℝ)^n * (1 + A^2) * B^(2*e+2) :=
        add_le_add hBP hXP
      _ = _ := by dsimp [D]; ring
  have hBX :
      1 + C + X + |p.direct| + (P.L.val : ℝ) + (P.J : ℝ) + μ⁻¹ = B + X := by
    dsimp [B]
    ring
  have hmain : allCost G n Z X μ C K W p P Q ≤ C₀ * (B + X)^d := by
    simpa only [hBX] using hall P μ C X p hC hX hμ hcap
  change allCost G n Z X μ C K W p P Q ≤
    (C₀ * D^d) * B^(d*(2*e+2))
  calc
    _ ≤ C₀ * (B + X)^d := hmain
    _ ≤ C₀ * (D * B^(2*e+2))^d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg hB₀ hX) hsum d) hC₀.le
    _ = _ := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm (2*e+2) d]
      ring

end YM.Integration.ActualUniformAllCostPolynomial
end
