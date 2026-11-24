import YM.MSbar.Pole.Analysis.Capacity

/-! Functions of rapid decay. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory
open scoped Topology ContDiff Classical
variable {E A F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup A]
variable {U : Set E} {p q : Price E} {f : E → F}

lemma cost_scale (p : Price E) (r s : ℕ) (x : E) (h : r≤s) : p x^r ≤ p x^s:= p.snap _ h
lemma bill_single {C : ℝ} {l : ℕ} (hp : 0 ≤ C) (h : ∀ x∈U, ‖f x‖≤C * q x^l) : Bills U q 1 f := by
  intro k; refine ⟨C,l,hp,?_⟩; simpa using h
lemma bill_byprice {s:Price E} (h : ∀ x∈U, s x ≤ p x) : Bills U p 1 s.val :=
  bill_single (l:=1) (C:=1) zero_le_one fun _ hx=>by
    change ‖s _‖ ≤ _; rw [Real.norm_of_nonneg (s.pos _).le,pow_one,one_mul]; exact h _ hx

lemma ticket_product (x:E×F): ticket (@id (E×F)) x ≤ (ticket (@Prod.fst E F)*ticket (@Prod.snd E F)) x := by
  rcases x with ⟨x,y⟩; change 1+ max ‖x‖ ‖y‖ ≤ (1+‖x‖)*(1+‖y‖)
  rcases le_or_gt ‖x‖ ‖y‖ with h|h
  · rw [max_eq_right h]; exact le_mul_of_one_le_left (by positivity) (by simp)
  rw [max_eq_left h.le]; exact le_mul_of_one_le_right (by positivity) (by simp)
section measure
variable [MeasurableSpace E] {μ : Measure E} [μ.HasTemperateGrowth]
lemma toll : Integrable (fun x:E => ((1+‖x‖)^μ.integrablePower)⁻¹) μ := by
  have hm := Measure.integrable_pow_neg_integrablePower μ
  have he (x:E) : (1+‖x‖)^(-(μ.integrablePower:ℝ)) = ((1+‖x‖)^μ.integrablePower)⁻¹ := by rw [Real.rpow_neg (by positivity),Real.rpow_natCast]
  simp_rw [he] at hm; exact hm
lemma rapid_pay (h : Bills U 1 (ticket (@id E)) f) (ho : MeasurableSet U) (hp : AEStronglyMeasurable f (μ.restrict U)) : IntegrableOn f U μ := by
  obtain ⟨C,l,hc,H⟩ := h μ.integrablePower
  refine (toll.integrableOn.mul_const (c:=C)).mono' hp ?_
  filter_upwards [ae_restrict_mem ho] with x hx; rw [mul_comm _ C, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]; simpa using H x hx
end measure
end YM.MSbar.Pole
