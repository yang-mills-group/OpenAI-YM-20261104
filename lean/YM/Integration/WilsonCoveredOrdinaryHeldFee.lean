import YM.Integration.WilsonReceivedCloseFoldedSlate

/-! Price a complete signed finite-to-cover ordinary comparison on a specified post.
The input bound on the complete source toll and the finite scalar weight appear once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoveredOrdinaryHeldFee
open Finset Marker Multi Comparison.RG02 Order
open scoped BigOperators Classical
open private cutoff from YM.Integration.WilsonReceivedCloseOrdinaryGrade

variable {V : Type} [DecidableEq V] (J : Census V)

def cost (a : ℕ) : ℝ := Fintype.card (parts J).Mode * (a:ℝ) * 4^a

def factor (a : ℕ) (C ε : ℝ) : ℝ := min 1 (ε / ((1+cost J a)*(1+|C|)))

theorem positive (a : ℕ) (C : ℝ) {ε:ℝ} (ep:0<ε) : 0 < factor J a C ε := by
  apply lt_min zero_lt_one
  unfold cost
  positivity

theorem controls (a : ℕ) (C : ℝ) {ε:ℝ} (ep:0<ε) : factor J a C ε * cost J a * C ≤ ε := by
  have c0 : 0 ≤ cost J a := by unfold cost; positivity
  have charge : cost J a*C ≤ (1+cost J a)*(1+|C|) := by
    have h:=mul_le_mul_of_nonneg_left (le_abs_self C) c0
    nlinarith only [h,abs_nonneg C,c0]
  calc
    _ ≤ factor J a C ε * ((1+cost J a)*(1+|C|)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left charge (positive J a C ep).le
    _ ≤ (ε / ((1+cost J a)*(1+|C|)))*((1+cost J a)*(1+|C|)) :=
      mul_le_mul_of_nonneg_right (min_le_right ..) (by positivity)
    _ = ε := div_mul_cancel₀ _ (by positivity)

theorem face (s:J.Mode) (a v w q:ℕ) {g η τ E : ℝ} (gp:0<g) (cold:g≤1) (hp:0 ≤ η) (small:η≤1)
    (live:s.val.card ≤ a) (toll:g^v ≤ τ) (nn:0 ≤ E)
    (ordinary:τ*E ≤ ∑ h ∈ shards J s, (h.val.card:ℝ)*(η*g^(q+w+v+a))*(g⁻¹+η*g^(q+w+v+a))^h.val.card) :
    E ≤ η*cost J a*g^(q+w) := by
  let r:=q+w+v
  have inv:g⁻¹ ≤ 3*g⁻¹ := by linarith only [inv_nonneg.mpr gp.le]
  have ηg:η*g^(r+a) ≤ g^(r+a) := mul_le_of_le_one_left (pow_nonneg gp.le _) small
  have sum : τ*E ≤ ((shards J s).card:ℝ)*(η*((a:ℝ)*4^a*g^r)) := calc
    _ ≤ _ := ordinary
    _ ≤ ∑ _h ∈ shards J s, η*((a:ℝ)*4^a*g^r) := Finset.sum_le_sum fun h hh => by
      have power:=pow_le_pow_left₀ (add_nonneg (inv_nonneg.mpr gp.le) (mul_nonneg hp (pow_nonneg gp.le _)))
        (by linarith only [ηg] : g⁻¹+η*g^(r+a) ≤ g⁻¹+g^(r+a)) h.val.card
      have hrs:=cutoff gp cold gp inv a r h.val.card ((WilsonFiniteOrdinaryTail.blocks s h hh).trans live)
      calc
        _ ≤ (h.val.card:ℝ)*(η*g^(r+a))*(g⁻¹+g^(r+a))^h.val.card :=
          mul_le_mul_of_nonneg_left power (by positivity)
        _ = η*((h.val.card:ℝ)*g^(r+a)*(g⁻¹+g^(r+a))^h.val.card) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hrs hp
    _ = _ := by simp
  have card : ((shards J s).card:ℝ) ≤ Fintype.card (parts J).Mode := by exact_mod_cast Finset.card_le_univ _
  apply (le_of_mul_le_mul_left _ (pow_pos gp v))
  calc
    _ ≤ τ*E := mul_le_mul_of_nonneg_right toll nn
    _ ≤ _ := sum
    _ ≤ (Fintype.card (parts J).Mode:ℝ)*(η*((a:ℝ)*4^a*g^r)) := mul_le_mul_of_nonneg_right card (by positivity)
    _ = _ := by dsimp [r,cost];rw [pow_add];ring

theorem signed (a v w q:ℕ) {C ε g:ℝ} (ep:0<ε) (gp:0<g) (cold:g≤1)
    (rows:Finset J.Mode) (price:J.Mode→ℝ) (f h c:J.Mode→ℂ)
    (paid:∀s∈rows,s.val.card ≤ a ∧ g^v ≤ price s)
    (ordinary:∀s∈rows,price s*‖f s-h s‖ ≤
      ∑ x ∈ shards J s,(x.val.card:ℝ)*(factor J a C ε*g^(q+w+v+a))*(g⁻¹+factor J a C ε*g^(q+w+v+a))^x.val.card)
    (weight:g^w*(∑s ∈ rows,‖c s‖) ≤ C) :
    ‖(∑s ∈ rows,c s*f s) - (∑s ∈ rows,c s*h s)‖ ≤ ε*g^q := by
  have hp:=positive J a C ep
  have each s hs := face J s a v w q gp cold hp.le (min_le_left ..) (paid s hs).1 (paid s hs).2
    (norm_nonneg _) (ordinary s hs)
  have nn : 0 ≤ factor J a C ε * cost J a := mul_nonneg hp.le (by unfold cost; positivity)
  calc
    _ ≤ (∑s ∈ rows,‖c s‖)*(factor J a C ε*cost J a*g^(q+w)) :=
      WilsonReceivedCloseFoldedSlate.combine rows c f h _ each
    _ = (factor J a C ε*cost J a*(g^w*(∑s ∈ rows,‖c s‖)))*g^q := by rw [pow_add];ring
    _ ≤ (factor J a C ε*cost J a*C)*g^q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left weight nn) (pow_nonneg gp.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (controls J a C ep) (pow_nonneg gp.le _)

end YM.Integration.WilsonCoveredOrdinaryHeldFee
