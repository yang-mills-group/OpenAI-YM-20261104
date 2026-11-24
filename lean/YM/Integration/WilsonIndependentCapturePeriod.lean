import YM.Integration.WilsonIndependentResidentWinding

/-! A marked field born at mesh τ retains its relative scale in the torus
winding estimate. The bound uses the period measured in the units of the
captured insertion, even for a nonbare original course. -/
noncomputable section
namespace YM.Integration.WilsonIndependentCapturePeriod
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient Spatial
open scoped ENNReal

private theorem coast {τ f y c p δ γ : ℝ} (ht : 0 < τ) (hf : 0 < f)
    (hy : f ≤ y) (hc : 0 < c) (hp : 0 < p) (hd : c*p ≤ δ)
    (hg : 0 ≤ γ) (hγ : γ ≤ 1) :
    (τ/f)^γ * (1 + δ/y)⁻¹ ≤ (c^γ)⁻¹ * (y/f) * (τ/p)^γ := by
  have y₀ := lt_of_lt_of_le hf hy
  have a₀ : 0 < c*p/y := by positivity
  have htoll : (c*p/y)^γ ≤ 1 + δ/y := by
    rcases le_total (c*p/y) 1 with h | h
    · exact (Real.rpow_le_one a₀.le h hg).trans (le_add_of_nonneg_right
        (div_nonneg ((mul_pos hc hp).le.trans hd) y₀.le))
    · exact (Real.rpow_le_self_of_one_le h hγ).trans
        ((div_le_div_of_nonneg_right hd y₀.le).trans (le_add_of_nonneg_left zero_le_one))
  calc
    _ ≤ (τ/f)^γ * ((c*p/y)^γ)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ (Real.rpow_pos_of_pos a₀ _) htoll) (by positivity)
    _ = (c^γ)⁻¹ * (y/f)^γ * (τ/p)^γ := by
      rw [Real.div_rpow ht.le hf.le, Real.div_rpow (mul_pos hc hp).le y₀.le,
          Real.mul_rpow hc.le hp.le, Real.div_rpow y₀.le hf.le, Real.div_rpow ht.le hp.le]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ ≤ _ := by
      gcongr
      exact Real.rpow_le_self_of_one_le ((one_le_div hf).mpr hy) hγ

variable {W : Type} {M : W → ℕ} {X Y : Page M → Type}
  {γ c : ℝ} {x : W → Room} (S : Sky X Y) (L : Meter W)

/-- Only the current unmarked scale ratio enters each winding payment. -/
theorem paid (dc : S.cushion c x) (hc : 0 < c) (hg : 0 ≤ γ) (hγ : γ ≤ 1)
    (big : ∀ j : Flap M, 1 ≤ S.l j.next)
    (scales : Poly (flapL M L) (fun j => ENNReal.ofReal (S.shift j)))
    (τ : W → ℝ) (ht : ∀ w, 0 < τ w) (gross : W → ℝ≥0∞) :
    Carry (flapL M L) (fun j => gross j.volW * ENNReal.ofReal ((τ j.volW / S.P j.volW)^γ))
      (fun j => (gross j.volW * ENNReal.ofReal ((τ j.volW / S.l j.prev)^γ)) *
        ((S.lifts.insideRoom S.ridge S.ridge_pos).toll (step_center M x) 1 j)⁻¹) := by
  let C := ENNReal.ofReal ((c^γ)⁻¹)
  refine ⟨fun j => C * ENNReal.ofReal (S.shift j),
    (Poly.standard _ (ENNReal.ofReal_ne_top (r := (c^γ)⁻¹))).mul scales, fun j => ?_⟩
  have hR : S.ridge j = S.l j.next := max_eq_right (big j)
  have hΔ : 0 ≤ singular (S.P j.volW) (x j.volW) := singular_nonneg ..
  have hr := S.hl j.next
  have co := coast (ht j.volW) (S.hl j.prev) (S.climb j) hc (S.hp j.volW) (dc j.volW) hg hγ
  calc
    _ = gross j.volW * (ENNReal.ofReal ((τ j.volW / S.l j.prev)^γ) *
      (ENNReal.ofReal (1 + singular (S.P j.volW) (x j.volW) / S.l j.next))⁻¹) := by
        unfold Post.toll amount
        change (_ * _) * ((ENNReal.ofReal (1 + _ / S.ridge j))^1)⁻¹ = _
        rw [hR, pow_one, mul_assoc]
        rfl
    _ ≤ gross j.volW * (C * ENNReal.ofReal (S.shift j) *
        ENNReal.ofReal ((τ j.volW / S.P j.volW)^γ)) := by
      apply mul_le_mul_right
      have h₀ : 0 ≤ (τ j.volW / S.l j.prev)^γ := Real.rpow_nonneg (div_nonneg (ht _).le (S.hl _).le) _
      rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 1 + singular (S.P j.volW) (x j.volW) / S.l j.next),
        ← ENNReal.ofReal_mul h₀]
      unfold C
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by
        have hs := S.shift_pos j
        positivity)]
      exact ENNReal.ofReal_le_ofReal co
    _ = _ := by dsimp only; ac_rfl

end YM.Integration.WilsonIndependentCapturePeriod
