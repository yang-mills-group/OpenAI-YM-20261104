import YM.GradedFar.Money
import YM.GradedFar.Width
/-!
# Spend before inverse (arithmetic supplier)

Trade the powers into r/g/T using the `g^(-B)` window. Inputs in this file about D,W and
symbols are pointwise implications. Not assuming or asserting anything about the physical prices
across regulator choices here. `combine` will be applied in the physical use with the constructed
Phase viewer, labels, Far positions, `A r g`, and **taking these remaining physical inputs on it**.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Budget
open Function Filter Set PowerSeries XSpace XSpace.Normalize
open scoped Topology BigOperators Classical
variable {G : Gauge} {h : ℕ}

lemma assemble_costs (Y W : ℂ) (D M : Sec G h →ₗ[ℂ] ℂ) (w c : Sec G h)
    {A B C E : ℝ} (hm : ‖Y-W‖ + rowPrice (D-M) ≤ A) (ht : width c ≤ B)
    (hc : ‖W-M c‖ ≤ C) (he : ‖Y-D w‖ ≤ E) :
    ‖Y-W‖ + rowPrice (D-M) + ‖Y-W-(D-M) c‖ + ‖Y-D w‖ + ‖Y-D c‖ ≤
      A*(1+2*(1+B)) + C + E := by
  have hp : 0 ≤ rowPrice (D-M) := norm_nonneg _
  have hf := norm_nonneg (Y-W)
  have hz : ‖(D-M) c‖ ≤ A*B := (row_le _ _).trans (mul_le_mul (by linarith) ht (width_nn _)
    ((add_nonneg hf hp).trans hm))
  have hu : ‖Y-W-(D-M) c‖ ≤ A*(1+B) := by linarith [norm_sub_le (Y-W) ((D-M) c)]
  have hv : ‖Y-D c‖ ≤ A*(1+B)+C := by
    rw [show Y-D c = (Y-W-(D-M) c) + (W-M c) from by rw [LinearMap.sub_apply]; abel]
    exact (norm_add_le ..).trans (add_le_add hu hc)
  linarith

namespace Budget
variable {a b B M C Q D η : ℝ} (ha : 0 < a) (hb : 0 < b) (hB : 0 < B) (hD : 0 ≤ D)
    (hm : 0 ≤ M) (hc : 0 ≤ C) (hq : 0 ≤ Q) (p P k j d : ℕ)
local notation "ℓ" => (𝓝[>] (0:ℝ))
include ha hb hB hD hm hc hq

/-- Powerful enough terms before paying the detector inverse. Multiplicative constants kept
independent of g,r. η needn't here be positive, but in the application use 0 < η < 1. -- note
that the T power at the target is *rpow*. -/
lemma powerful (h : ℕ) (hf : P+D+3 < B*(1-η)) (hp : P+B*(d+h+η)+5 < p) :
    ∃ n : ℕ, ∀ᶠ g : ℝ in ℓ, ∀ T, receding g B a b T →
      let target := g^P * T^(-(h:ℝ)-η)
      M*T^d*g^(p+1)*(1+Real.log T)^k ≤ target ∧
      C*((T^(h+1))⁻¹+g^(p+1))*(1+Real.log T)^j ≤ target+target ∧
      ∀ r : ℝ, r ≤ g^n → Q*g^(-D)*(r*T+(T^(h+1))⁻¹) ≤ target+target := by
  obtain ⟨n,hn⟩ := exists_nat_gt (B*(1-(-(h:ℝ)-η)) + D + P)
  let y := - (h:ℝ)-η
  have h0 : B*((d:ℝ)-y) < ((p+1:ℕ):ℝ)-P := by push_cast; unfold y; linarith
  have h1 : B*(0-y) < ((p+1:ℕ):ℝ)-P := lt_of_le_of_lt (by gcongr; exact Nat.cast_nonneg _) h0
  have h2 : B*(-((h+1:ℕ):ℝ)-y) < -D-P := by push_cast; unfold y; linarith
  have h3 : B*(-((h+1:ℕ):ℝ)-y) < 0-P := by linarith
  have h4 : B*(1-y) < (-D + n)-P := by unfold y; linarith
  refine ⟨n, ?_⟩
  filter_upwards [trade hB ha hb M hm k h0, trade hB ha hb C hc j h1,
    trade hB ha hb Q hq 0 h2, trade hB ha hb C hc j h3, trade hB ha hb Q hq 0 h4,
    self_mem_nhdsWithin] with g h0 h1 h2 h3 h4 h5 T he
  have hg : 0 < g := h5
  have ht := lt_of_lt_of_le (by positivity : 0 < a*g^(-B)) he.1
  specialize h0 T he; specialize h1 T he; specialize h2 T he; specialize h3 T he; specialize h4 T he
  rw [Real.rpow_add hg] at h4
  rw [Real.rpow_neg ht.le] at h2 h3
  simp only [Real.rpow_natCast, Real.rpow_zero, Real.rpow_one, mul_one, pow_zero] at *
  rw [mul_right_comm M]; refine ⟨h0,?_,?_⟩
  · rw [mul_add, add_mul]; exact add_le_add h3 h1
  intro r hr
  rw [mul_add]
  refine add_le_add ?_ h2
  calc _ ≤ Q*g^(-D)*(g^n*T) := by gcongr
       _ ≤ _ := by rwa [← mul_assoc (Q*g^(-D)), mul_assoc Q]

lemma combine (η_condition : P+D+3 < B*(1-η)) (order : P+B*(d+h+η)+5 < p) {c_cap : ℝ}
    (hbc : 0 ≤ c_cap) : ∃ L : ℝ, 0 < L ∧ ∃ n : ℕ,
      ∀ᶠ g : ℝ in ℓ, ∀ T, receding g B a b T → ∀ r, r ≤ g^n →
      ∀ (Y W : ℂ) (V V' : Sec G h →ₗ[ℂ] ℂ) (w c : Sec G h), width c ≤ c_cap →
      ‖Y-W‖ + rowPrice (V-V') ≤ M*T^d*g^(p+1)*(1+Real.log T)^k →
      ‖W-V' c‖ ≤ C*((T^(h+1))⁻¹+g^(p+1))*(1+Real.log T)^j →
      ‖Y-V w‖ ≤ Q*g^(-D)*(r*T+(T^(h+1))⁻¹) →
      ‖Y-W‖ + rowPrice (V-V') + ‖Y-W-(V-V') c‖ + ‖Y-V w‖ + ‖Y-V c‖ ≤ L*g^P*T^(-(h:ℝ)-η) := by
  obtain ⟨n,late⟩ := powerful ha hb hB hD hm hc hq p P k j d h η_condition order
  refine ⟨7 + 2*c_cap, by positivity, n, late.mono fun g hg T hT r hr Y W V V' w c hc hm hj ht => ?_⟩
  obtain ⟨a,b,d⟩ := hg T hT
  exact (assemble_costs _ _ _ _ _ _ (hm.trans a) hc (hj.trans b) (ht.trans (d r hr))).trans_eq (by ring)
end Budget
end YM.FVA2.GradedFar
