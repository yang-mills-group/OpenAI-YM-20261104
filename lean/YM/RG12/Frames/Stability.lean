import YM.RG12.Frames.Gram

/-! # Explicit reflection-price perturbation budgets on the pivot tests

`nonsingular` only prices endpoints of a step of filtration transport. For pricing the
transition, `step_ratio` uses a quantitative estimate comparing two near-neighbor
geometries (& optional sheared configurations), not a vague proof that each tends to free.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Frames.Gram
open Function Finset Filter
open scoped Topology BigOperators
variable {d : ℕ} {V : Grade d → Type} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
variable {F E : Type} [AddCommGroup F] [Module ℂ F] {P Q : Square F}
variable {Y : Col V →ₗ[ℂ] F}

/-- Stability around an independent leading Gram (e.g. fixed free grade chart, both
energy-rescaled pivots and profiles/weights fixed under dilation). -/
lemma nonsingular {K : ℝ} (G : Col V → ℝ) (hs : 1 ≤ K)
    (hg : ∀ x, G x ≤ K*‖x‖^2 ∧ ‖x‖^2 ≤ K*G x)
    (hp : ∀ x, |P.eval (Y x) - G x| ≤ (2*K)⁻¹ * ‖x‖^2) : Regular P Y (2*K) := by
  have hk := zero_lt_one.trans_le hs
  have hf : 0 < 2*K := mul_pos zero_lt_two hk
  have hi : (2*K)⁻¹ ≤ K := (inv_le_one_of_one_le₀ (by linarith only [hs])).trans hs
  refine ⟨by linarith only [hs],fun x=> ?_, fun x=> ?_⟩
  · obtain ⟨-,he⟩:= abs_le.mp (hp x); have hc := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖x‖)
    linarith only [he,hc,(hg x).1]
  obtain ⟨he,-⟩:= abs_le.mp (hp x)
  have h:= mul_le_mul_of_nonneg_left he hf.le
  field_simp at h; nlinarith only [h, (hg x).2]

/-- Uses sensitivity `a` per consecutive log-length step. The estimates compare
measurements at nearby scales on the later basis, allowing off-degree change as above.
No log factors in `a` accumulating per step. Returns power prices in amplitude **not
squared**. `s` = log age, `r` its ratio. -/
lemma step_ratio (X : Col V → F) {K s a r: ℝ} {p:ℕ} (hh : Regular Q Y K)
    (hs : 1 ≤ s) (hr : 1+s⁻¹ ≤ r)
    (ha : a*K ≤ p) (he : 2*p ≤ s) (hx : 0 ≤ a)
    (hp : ∀ x, |P.eval (X x) - Q.eval (Y x)| ≤ (a/s) * ‖x‖^2) (x : Col V) :
    let G := Q.eval (Y x); let G' := P.eval (X x)
    Real.sqrt G' ≤ r^(2*p) * Real.sqrt G ∧ Real.sqrt G ≤ r^(2*p)*Real.sqrt G' :=by
  intro G G'; let t:= (p:ℝ)/s
  have ht :0 ≤ t:= by positivity
  have hL:= zero_lt_one.trans_le hs
  have hr':1 ≤ r:= (le_add_of_nonneg_right (inv_nonneg.mpr hL.le)).trans hr
  have hk := zero_lt_one.trans_le hh.legal
  have hG:0 ≤ G := nonneg_of_mul_nonneg_right ((sq_nonneg _).trans (hh.coerc x)) hk
  have hF := abs_le.mp (hp x)
  have hz : 2*t ≤ 1:= by unfold t; rw [← mul_div_assoc,div_le_one hL]; exact he
  have hu : a/s*‖x‖^2 ≤ t*G:= by
    apply (mul_le_mul_of_nonneg_left (hh.coerc x) (div_nonneg hx hL.le)).trans
    change _ ≤ (p:ℝ)/s*G
    rw [← mul_assoc,div_mul_eq_mul_div]; exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ha hL.le) hG
  have hΓ: G' ≤ (1+t)*G ∧ (1-t)*G ≤ G':= by dsimp only [G'] at *; constructor <;> linarith only [hu,hF.1,hF.2]
  have hG' : 0 ≤ G':=(mul_nonneg (by linarith only [hz]) hG).trans hΓ.2
  have hi : (1-t)*(1+2*t) ≥ 1:=by nlinarith only [ht,hz]
  have hG₁ : G ≤ (1+2*t)*G':=by
    calc
      _ ≤ ((1-t)*(1+2*t))*G:=le_mul_of_one_le_left hG hi
      _ = (1+2*t)*((1-t)*G):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_left hΓ.2 (by positivity)
  have hR : 1+2*t ≤ r^(2*p):=by
    unfold t; rw [div_eq_mul_inv, ← mul_assoc, show (2:ℝ)*(p:ℝ)=↑(2*p) from by simp] -- cast two not exposed?
    exact (one_add_mul_le_pow (by have := inv_pos.mpr hL; linarith only [this] : (-2:ℝ) ≤ s⁻¹) _).trans (pow_le_pow_left₀ (by positivity) hr _)
  have hb := one_le_pow₀ (n:=2*p) hr';
  have he {x y:ℝ} (hx:0 ≤ x) (hy:0 ≤ y) (he:x ≤ (1+2*t)*y): Real.sqrt x ≤ r^(2*p)*Real.sqrt y:= by
    apply le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (mul_nonneg (zero_le_one.trans hb) (Real.sqrt_nonneg _))
    rw [Real.sq_sqrt hx, mul_pow,Real.sq_sqrt hy]; exact he.trans (mul_le_mul_of_nonneg_right (hR.trans
      (le_self_pow₀ hb (by decide))) hy)
  refine ⟨he hG' hG (hΓ.1.trans (mul_le_mul_of_nonneg_right ?_ hG)),he hG hG' hG₁⟩
  linarith only [ht]
end YM.RG12.Frames.Gram
