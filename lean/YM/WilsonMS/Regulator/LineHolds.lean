import YM.WilsonMS.Regulator.Handholds
/-!
# Hölder bookkeeping for the continuum line and contracted charts
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Climb
open Function Set Filter MeasureTheory Real Finset
open MS MS.Plane MS.Land MS.Landau MS.Landau.Detect MS.Heat MS.Tone
open MS.Latch MS.Latch.Job MS.Rake MS.Orbit MS.Book MS.Osc MS.Osc.Snap MS.Vane MS.City
variable {G : Gauge} {E X : Type} [NormedAddCommGroup E] {T : X → X → ℝ → Prop}

lemma price_zpow (t : ℝ) (z : ℤ) : exp t ^ z ≤ exp ((z.natAbs : ℝ) * |t|) := by
  rw [a_e]
  apply exp_monotone
  refine (le_abs_self (t * (z : ℝ))).trans ?_
  rw [abs_mul, mul_comm]
  exact
    Eq.le
      (by
        congr
        rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast])

/-- Rapid but with losses exponential in log-time; here enough for
Hölder-insertion estimates. -/
lemma Planet_R (i j : BH G) (m : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧ ∃ k : ℕ, ∀ (t : ℝ) (p : QP), ‖PlanetD G t i j p‖ ≤ C * exp (k * |t|) / heft p ^ m := by
  let S : MS.Scale ℝ :=
    { length := exp, pos := exp_pos, basic := fun _ => 1, one_le := fun _ => le_rfl }
  obtain ⟨C, hC, k, hK⟩ := ((cost_D (a := id) (G := G) (S := S) (fun _ => rfl)) i j m).norm_cost
  let z := (4 : ℤ) - wfield i - wfield j
  refine ⟨C, hC.le, z.natAbs + m, ?_⟩
  intro t p
  have hu := hK t p trivial
  change ‖PlanetD G t i j p‖ ≤ C * 1 ^ k * (exp t ^ z * 1 / (1 + exp t * ‖p‖) ^ m) at hu
  rw [one_pow, mul_one, mul_one, ← mul_div_assoc] at hu
  have hv := exp_pos t
  have hv' := exp_pos (-|t|)
  have hz := hefty0 p
  have hL : exp (-|t|) * heft p ≤ 1 + exp t * ‖p‖ := by
    unfold heft
    rw [mul_add, mul_one]
    exact
      add_le_add (Real.exp_le_one_iff.mpr (by simp))
        (mul_le_mul_of_nonneg_right (exp_monotone (neg_abs_le t)) (norm_nonneg p))
  apply hu.trans
  calc
    _ ≤ C * exp (z.natAbs * |t|) / (exp (-|t|) * heft p) ^ m := by
      gcongr
      exact price_zpow ..
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul, Nat.cast_add, add_mul, Real.exp_add, mul_neg, exp_neg]
      field_simp

lemma Planet_tame (i j : BH G) : Tames T (fun _ t p => PlanetD G t i j p) := by
  refine ⟨?_, holding _⟩
  obtain ⟨C, hC, n, h⟩ := Planet_R i j 0
  refine ⟨C, hC, n, fun x t p => (h t p).trans ?_⟩
  have hz := hefty p
  rw [rope_exp]
  simp only [pow_zero, div_one, Pi.one_apply, mul_one]
  rw [← mul_assoc]
  exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hz)

lemma rope_pair (t : ℝ) (v : QP × E) : rope t v ≤ rope t v.2 * heft v.1 := by
  unfold rope
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  unfold heft
  simp only [Prod.norm_def]
  have hz := norm_nonneg v.1
  have hx := norm_nonneg v.2
  rcases le_total ‖v.1‖ ‖v.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith
  rw [max_eq_left h]
  nlinarith

/-- Integration weight (unscaled). -/
def skin (p : QP) :=
  (heft p ^ 5)⁻¹

lemma skin_mem : Integrable skin planeF := by
  have h := (Tall (Job.single Unit) 5 (by omega)).integrable ()
  convert h using 1
  funext p
  simp [skin, Scale.dust, Scale.weight, Job.single, heft]

lemma skin_p (p : QP) : 0 < skin p :=
  inv_pos.mpr (pow_pos (hefty0 _) _)

lemma Planet_pair_le {C H : ℝ} (hH : 0 ≤ H) (hc : 0 ≤ C) (t : ℝ) (n k : ℕ) (v : QP × E) :
    C * exp (k * |t|) / heft v.1 ^ (n + 5) * (H * rope t v ^ n) ≤
      C * H * rope t v.2 ^ (k + n) * skin v.1 := by
  have hx := ropey0 t v
  have ht := ropey0 t v.2
  have hz := hefty0 v.1
  calc
    _ ≤ C * exp (k * |t|) / heft v.1 ^ (n + 5) * (H * (rope t v.2 * heft v.1) ^ n) := by
      gcongr
      exact rope_pair ..
    _ = C * H * exp (k * |t|) * rope t v.2 ^ n * skin v.1 := by
      unfold skin
      rw [pow_add, mul_pow]
      field_simp
    _ ≤ _ := by
      rw [pow_add _ k n, rope_exp t v.2 k, ← mul_assoc _ _ (rope _ _ ^ n), ←
        mul_assoc (C * H) _ (heft _ ^ k)]
      exact
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (hefty v.2))) (pow_nonneg ht.le _))
          (skin_p v.1).le

variable {L : Profile X (QP × E)}

def Winter (T) (L : Profile X (QP × E)) :=
  Handles T (fun t p => rope t p.2) (fun p => skin p.1) L

lemma Planet_pair (h : Tames T L) (i j : BH G) :
    Winter T (fun x t p => PlanetD G t i j p.1 * L x t p) := by
  obtain ⟨⟨C, hC, n, h⟩, a, ha, D, hD, m, hs⟩ := h
  simp only [Pi.one_apply, mul_one] at hs h
  obtain ⟨R, hR, k, hV⟩ := Planet_R i j (n + 5)
  obtain ⟨U, hU, M, hT⟩ := Planet_R i j (m + 5)
  refine ⟨⟨R * C, by positivity, k + n, fun x t p => ?_⟩, a, ha, U * D, by positivity, M + m, ?_⟩
  · rw [norm_mul]
    have ht := hefty0 p.1
    exact (mul_le_mul (hV ..) (h ..) (norm_nonneg _) (by positivity)).trans (Planet_pair_le hC hR ..)
  intro x y r hr h t p
  rw [← mul_sub, norm_mul]
  have ht := hefty0 p.1
  exact
    (mul_le_mul (hT ..) (hs _ _ _ hr h t p) (norm_nonneg _) (by positivity)).trans
      ((Planet_pair_le (n := m) (show 0 ≤ D * exp (-a * r) from (by positivity)) hU t M p).trans_eq
        (by ring))

lemma Winter.rescue (h : Winter T L) (hp : ∀ x t p, Integrable (fun q => L x t (q, p)) planeF) :
    Tames T (fun x t p => ∫ q, L x t (q, p) ∂planeF) := by
  obtain ⟨⟨C, hC, n, h⟩, a, ha, D, hD, m, hM⟩ := h
  let R := ∫ q, skin q ∂planeF
  have hR : 0 ≤ R := integral_nonneg (fun p => (skin_p p).le)
  refine ⟨⟨C * R, by positivity, n, fun x t p => ?_⟩, a, ha, D * R, by positivity, m, ?_⟩
  · refine
      (norm_integral_le_of_norm_le (skin_mem.const_mul (C * rope t p ^ n))
            (Eventually.of_forall fun q => h x t (q, p))).trans_eq
        ?_
    rw [integral_const_mul]
    unfold R
    simp only [Pi.one_apply]
    ring
  intro x y r hr hx t p
  rw [← integral_sub (hp ..) (hp ..)]
  refine
    (norm_integral_le_of_norm_le (skin_mem.const_mul (D * exp (-a * r) * rope t p ^ m))
          (Eventually.of_forall fun q => hM _ _ _ hr hx t (q, p))).trans_eq
      ?_
  rw [integral_const_mul]
  unfold R
  simp only [Pi.one_apply]
  ring
end YM.WilsonMS.Climb
