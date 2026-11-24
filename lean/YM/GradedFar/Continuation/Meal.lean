import YM.GradedFar.Continuation.Stretch

/-! Pay each type of term contributing to (M.3), keep the same growing T. -/
namespace YM.FVA2.GradedFar.Continuation
namespace Stretch
noncomputable section
open Filter Set Topology Real Function
open Window (windows)
open scoped Topology
variable {G : Gauge}
/-- Target upper bound (without constant), also notation on real λ, η. -/
def till (G : Gauge) (P h : ℕ) (η : ℝ) (w : Window) := gYM G w.1^P * exp w.2 ^ (-((h:ℝ)+η))

/- Space in the choice of exponents. Choose
B independently of p, after the true spatial estimate's geometry
parameter D (and P, etc.). -/
def Stiff (B : ℝ) (P : ℕ) (η D : ℝ) : Prop := B*(1-η) > P+D+3
-- `v` the cap sum (`D_E`)
def Deep (p P : ℕ) (B : ℝ) (v h : ℕ) (η : ℝ) : Prop := P+B*((v:ℝ)+h+η)+5 < p
lemma can_stiffen (P : ℕ) {η : ℝ} (hη : η < 1) (D : ℝ) :
    ∀ᶠ B in atTop, Stiff B P η D ∧ 0<B := by
  have he : Tendsto (fun B : ℝ => B*(1-η)) atTop atTop := tendsto_id.atTop_mul_const (by linarith)
  exact (he.eventually_gt_atTop (P+D+3)).and (eventually_gt_atTop 0)
lemma can_deepen (P : ℕ) (B : ℝ) (v h : ℕ) (η : ℝ) : ∀ᶠ p in atTop, Deep p P B v h η := by
  exact tendsto_natCast_atTop_atTop.eventually_gt_atTop _

variable (simple : G.Simple)
local notation "g" => gYM G
variable {k C B : ℝ} (hk : 0<k) (hC : 0<C) (hB : 0<B) {P p h v : ℕ} {η D : ℝ}

include simple hk hC hB
-- pay with any fixed multiplier
lemma first_cost (a : ℕ) (hp : Deep p P B v h η) {D' : ℝ} (hD' : 0<D') :
    ∀ᶠ w in windows (band G k C B),
      D' * (exp w.2)^v * g w.1^(p+1) * (1+w.2)^a ≤ till G P h η w := by
  have he : (P:ℝ)-B*(-(h+η)) < ((p+1:ℕ):ℝ)-B*(v:ℝ) := by
    push_cast; unfold Deep at hp; linarith
  filter_upwards [trade simple hk hC hB he a hD'] with w hw
  unfold till; simp only [rpow_natCast] at hw ⊢; convert hw using 1; ring
lemma residual_cost (hD : 0 ≤ D) (hb : Stiff B P η D) (hp : Deep p P B v h η) (a : ℕ) {D' : ℝ} (hD' : 0<D') :
    ∀ᶠ w in windows (band G k C B),
      D'*((exp w.2)⁻¹^(h+1) + g w.1^(p+1)) * (1+w.2)^a ≤ 2*till G P h η w := by
  have he : (P:ℝ)-B*(-(h+η)) < 0-B*(-(((h+1:ℕ):ℝ))) := by
    push_cast; unfold Stiff at hb; linarith
  have hp' : Deep p P B 0 h η := by
    have hu : 0 ≤ B*v := by positivity
    unfold Deep at hp ⊢; push_cast; linarith
  filter_upwards [trade simple hk hC hB he a hD', first_cost simple hk hC hB a hp' hD'] with w hw hp
  rw [two_mul,mul_add,add_mul]; rw [Real.rpow_zero,mul_one,rpow_natCast,rpow_neg (exp_pos _|>.le),rpow_natCast] at hw
  rw [pow_zero, mul_one] at hp; refine add_le_add ?_ hp
  unfold till; rw [inv_pow]; exact (le_of_eq (by ring : D' * _ * _ = D' * (1+w.2)^a * ((exp w.2)^(h+1))⁻¹)).trans hw

/-- The physical spatial error g^(-D)*(s + T^(-h-1)), s here being *physical Coarse*. -/
lemma spatial_cost (hb : Stiff B P η D) {D' : ℝ} (hD' : 0<D') :
    ∀ᶠ w in windows (band G k C B),
      D'*(g w.1)^(-D) * (w.1*exp w.2 + (exp w.2)⁻¹^(h+1)) ≤ 2*till G P h η w := by
  let v : ℝ := (P:ℝ)+D+B*((h:ℝ)+1+η)+1
  have he : (P:ℝ)-B*(-(h+η)) < -D-B*(-(((h+1:ℕ):ℝ))) := by
    unfold Stiff at hb; push_cast; linarith
  have hf : (P:ℝ)-B*(-(h+η)) < (-D+v)-B*1 := by unfold v; linarith
  filter_upwards [trade simple hk hC hB he 0 hD',trade simple hk hC hB hf 0 hD',
    (Window.windows_short _).eventually (small_root simple v), (Window.windows_short _).eventually (positive_g simple)]
    with w hw hp hr hg
  change w.1 ≤ _ at hr; change 0<g w.1 at hg
  rw [mul_add,two_mul]; unfold till
  simp only [pow_zero,rpow_natCast,rpow_neg (exp_pos _|>.le), rpow_one,mul_one] at hp hw ⊢ -- changed target exponent on till both
  refine add_le_add ?_ (by rw [inv_pow]; exact hw)
  calc
    D'*(g w.1)^(-D) * (w.1 * exp w.2) ≤ D'*(g w.1)^(-D) * ((g w.1)^v * exp w.2) := by

      gcongr; exact hr
    _ = D'*(g w.1)^(-D+v)*exp w.2 := by rw [rpow_add hg (-D) v]; ring
    _ ≤ _ := hp
end
end Stretch
end YM.FVA2.GradedFar.Continuation
