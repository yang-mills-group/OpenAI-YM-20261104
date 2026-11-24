import YM.WilsonMS.Regulator.HoldCycles
/-!
# Integrating Holder errors at the UV end
Although source radii themselves lose powers when positions move, combine two
east budgets, rough Hölder (grows) and separation (decays without factor of
the step in positions). Then every past half-line cost is summable. Standard
interpolation, written in cutoff form.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Climb
open Function Set Filter MeasureTheory Real Finset
open MS MS.Plane MS.Landau MS.Landau.Detect MS.Land MS.Heat MS.Tone MS.Koszul
open MS.Latch MS.Latch.Job MS.Rake MS.Orbit MS.Book MS.Osc MS.Osc.Snap MS.Vane MS.City MS.Dial MS.Tide
open MS.Local.Physical Wire Belt Geo Flux
variable {G : Gauge} {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : X → X → ℝ → Prop} {F : Glade G X} {μ : ℝ}
open scoped ContDiff
set_option quotPrecheck false
local notation "Rρ" => frameF X μ

lemma pastU (w : Wired G E) (h : Came Rρ false F) (H : Sticky T (liftC F w)) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∃ a : ℝ,
          0 < a ∧
            ∃ n : ℕ,
              ∀ x y r,
                0 ≤ r →
                  T x y r →
                    ∀ s t : ℝ,
                      s ≤ t →
                        ∀ p,
                          ‖liftC F w x s p - liftC F w y s p‖ ≤
                            C * exp (-a * r) * rope t p ^ n * exp ((1 / 4 : ℝ) * s) := by
  obtain ⟨b, hb, C, hC, n, hp⟩ := H
  obtain ⟨D, hD, m, hq⟩ := sepE F h w
  let M : ℝ := n
  let k := b / 2 / (M + 1)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hk : 0 < k := by
    unfold k
    positivity
  have hr : k * (M + 1) = b / 2 := div_mul_cancel₀ _ (by positivity)
  let a := min (k / 4) (b / 2)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hs : a ≤ k / 4 := min_le_left ..
  have he : a ≤ b / 2 := min_le_right ..
  let B := max C (D + D)
  let v := max m n
  have hV (t : ℝ) (p : E) (i : ℕ) (hi : i ≤ v) : heft p ^ i ≤ rope t p ^ v := by
    apply le_trans (b := rope t p ^ i) ?_ ?_
    · have hm := hefty0 p
      gcongr
      exact le_mul_of_one_le_left hm.le (Real.one_le_exp (by positivity))
    exact pow_le_pow_right₀ (ropey t p) hi
  refine ⟨B, hC.trans (le_max_left ..), a, ha, v, ?_⟩
  intro x y r hx hT s t hL p
  have hv := ropey0 t p
  have hz := hefty0 p
  have hu := hp _ _ r hx hT s p
  rw [Pi.one_apply, mul_one] at hu
  by_cases hN : s ≤ 0
  · by_cases hc : |s| ≤ k * r
    · refine hu.trans ?_
      rw [rope_exp, ← mul_assoc, mul_assoc C, ← exp_add, mul_right_comm (B * _)]
      have ht : exp (-b * r + n * |s|) ≤ exp (-a * r) * exp ((1 / 4 : ℝ) * s) := by
        rw [← exp_add]
        apply exp_monotone
        rw [abs_of_nonpos hN] at *
        change _ + M * _ ≤ _
        have h80 : a * r ≤ b / 2 * r := mul_le_mul_of_nonneg_right he hx
        have hZ := congr_arg (· * r) hr
        nlinarith [mul_le_mul_of_nonneg_left hc hM]
      rw [mul_assoc B _ _]
      gcongr
      · exact le_max_left ..
      exact hV t p _ (le_max_right ..)
    have hc := le_of_not_ge hc
    rw [abs_of_nonpos hN] at hc
    refine (norm_sub_le ..).trans ((add_le_add (hq x s hN p) (hq y s hN p)).trans ?_)
    have ht : exp ((1 / 2 : ℝ) * s) ≤ exp (-a * r) * exp ((1 / 4 : ℝ) * s) := by
      rw [← exp_add]
      apply exp_monotone
      nlinarith [mul_le_mul_of_nonneg_right hs hx]
    rw [← add_mul, ← add_mul, mul_right_comm (B * _)]
    rw [mul_assoc B _ _]
    gcongr
    · exact le_max_right ..
    exact hV t p _ (le_max_left ..)
  have hvS : 0 ≤ s := le_of_not_ge hN
  have ht := hvS.trans hL
  have hU : rope s p ^ n ≤ rope t p ^ v := by
    apply le_trans (?_ : _ ≤ rope t p ^ n) (pow_le_pow_right₀ (ropey t p) (le_max_right m n))
    have h := ropey0 s p
    gcongr
    unfold rope
    gcongr
  refine
    hu.trans
      (le_trans ?_
        (le_mul_of_one_le_right (b := exp (1 / 4 * s))
          (by
            have hz : 0 ≤ B := hC.trans (le_max_left ..)
            positivity)
          (Real.one_le_exp (by positivity))))
  gcongr
  · exact pow_nonneg (ropey0 s p).le _
  · exact le_max_left ..
  linarith

lemma riverHeld (hT : Came Rρ false F) (ht : train false F) (w : Wired G E)
    (h : Sticky T (liftC F w)) : Sticky T (liftC (river F) w) := by
  obtain ⟨C, hC, a, ha, n, hv⟩ := pastU w hT h
  refine ⟨a, ha, C * 4, by positivity, n + 1, ?_⟩
  intro x y r hr h t p
  unfold liftC river
  rw [Pi.one_apply, mul_one, ←
    integral_sub (ht _ _ _ (fun i => Bool.noConfusion i)) (ht _ _ _ (fun i => Bool.noConfusion i))]
  let M := C * exp (-a * r) * rope t p ^ n
  have he := ropey0 t p
  have hM : 0 ≤ M := by
    unfold M
    positivity
  refine
    (norm_integral_le_of_norm_le
          ((integrableOn_exp_mul_Iic (a := (1 / 4 : ℝ)) (by norm_num) t).const_mul M)
          ((ae_restrict_mem measurableSet_Iic).mono fun i hi => hv x y r hr h i t hi p)).trans
      ?_
  rw [integral_const_mul, integral_exp_mul_Iic (by norm_num)]
  have hU : exp ((1 / 4 : ℝ) * t) ≤ rope t p := by
    apply le_trans ?_ (show exp |t| ≤ rope t p from le_mul_of_one_le_right (exp_pos _).le (hefty _))
    apply exp_monotone
    linarith [abs_nonneg t, le_abs_self t]
  calc
    _ ≤ M * (4 * rope t p) := by
      gcongr
      linarith only [hU]
    _ = _ := by
      unfold M
      ring
end YM.WilsonMS.Climb
