import YM.Integration.FVA1Physical.Round2.ResetRadial

/-! The actual coupling and field re-expansion can be applied to one
summably represented Wilson coefficient bank. Only pre-reset readings
at a finite radial grid for each old order enter the summability premise. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Finset Filter Function MvPolynomial MSbar MSbar.Rolling MSbar.Bakery MSbar.Cacao MSbar.Wave
open MSbar.Bakery.Portal Comparison.RG02 PertExtension.Series PertExtension.Series.Tested
open scoped BigOperators Classical Topology ContDiff
variable {σ α : Type} [Fintype σ]

omit [Fintype σ] in
private theorem ticket_at (b : PowerSeries ℝ) (V : PowerSeries (Pot σ)) (i : ℕ) (x : View σ) :
    eval x (PowerSeries.coeff i (ticket b V)) =
      ∑ j∈range (i+1), ∑ k∈range (j+2+1), PowerSeries.coeff (i-j) (b^k * b⁻¹^j) *
        eval x (homogeneousComponent k (PowerSeries.coeff j V)) := by
  simp only [ticket,fare,PowerSeries.coeff_mk,map_sum,←C_mul',map_mul,eval_C]

/-- Sum adjacent-coupling outputs on the independent Wilson bank through
the prescribed order and at one common coarse field. -/
theorem reset_summable_catalogue {H : ℝ → ℝ} {b : PowerSeries ℝ}
    (V : α → PowerSeries (Pot σ)) (W : PowerSeries (Pot σ)) (r : ℕ)
    (h₀ : H 0 = 1) (hb : PowerSeries.coeff 0 b = 1) (hs : ContDiffAt ℝ ω H 0)
    (hH : Approx H b r) (hV : ∀ a, Expanse (V a) 1 r) (hW : Expanse W 1 r)
    (x : View σ)
    (readings : ∀ j≤r, ∀ t : Fin (j+2+1), HasSum
      (fun a => eval ((t.val : ℝ) • x) (PowerSeries.coeff j (V a)))
      (eval ((t.val : ℝ) • x) (PowerSeries.coeff j W))) {i : ℕ} (hi : i ≤ r) :
    HasSum (fun a => Adjacent.born (displayed (V a)) (sceneGerm H hs h₀) 0 r i x)
      (displayed (ticket b W) i x) := by
  have rows (j : ℕ) (hj : j ≤ i) (k : ℕ) (hk : k ∈ range (j+2+1)) :=
    radial_hasSum (fun a=>PowerSeries.coeff j (V a)) (PowerSeries.coeff j W) x
      (fun a => show _ ≤ j+2 by simpa only [one_mul] using (hV a).profile j (hj.trans hi))
      (show _ ≤ j+2 by simpa only [one_mul] using hW.profile j (hj.trans hi))
      (readings j (hj.trans hi)) (⟨k,mem_range.mp hk⟩ : Fin (j+2+1))
  have atTicket : HasSum (fun a => eval x (PowerSeries.coeff i (ticket b (V a))))
      (eval x (PowerSeries.coeff i (ticket b W))) := by
    simp_rw [ticket_at]
    apply hasSum_sum
    intro j hj
    refine hasSum_sum fun k hk => ?_
    exact (rows j (Nat.lt_succ_iff.mp (mem_range.mp hj)) k hk).mul_left _
  have lifted := atTicket.mapL Complex.ofRealCLM
  exact lifted.congr_fun fun a => ticket_adjacent (V a) r h₀ hb hs hH (hV a) x hi
end YM.Integration.FVA1Physical.Round2
