import YM.Integration.WilsonSignedReportPrice
import YM.RG16.Unmasked.Pace
import YM.OPE.Therm.Request

/-! The true radius-dependent RG16 cell need not be the first stock port.
Its two geometric bounds and the original Wilson thermal price suffice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingReportTreasury

open Function Filter Set Asymptotics Lattice Wilson RG RG16 RG16.Literal OPE MergeProof Accent
open scoped Topology BigOperators
variable {G : Gauge} (C : Family G) (hG : G.Simple)
include hG
local notation "β" => C.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda C.path.levels

theorem small (H : ℝ) (n : ℕ) {δ : ℝ} (hd : 0 < δ) :
    ∀ᶠ k in atTop, H*(Λ k)^n ≤ δ*C.S.scale k := by
  let b := C.path.levels.clock.bar
  have hβ : Tendsto β atTop atTop := tendsto_atTop_add_const_left _ _
    (C.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
  have hbar : (fun _ : ℕ => b) =o[atTop] C.S.scale :=
    (isLittleO_const_id_atTop b).comp_tendsto C.S.divergent
  have hβs : β =O[atTop] C.S.scale :=
    hbar.isBigO.add ((isBigO_refl C.S.scale _).const_mul_left G.slopeConstant)
  have hl := ((Real.isLittleO_pow_log_id_atTop (n:=n)).comp_tendsto hβ).trans_isBigO hβs
  have sale := (hl.const_mul_left (|H| * 3^n)).def hd
  filter_upwards [sale,(Real.tendsto_log_atTop.comp hβ).eventually_ge_atTop 1,
    C.S.divergent.eventually_ge_atTop 0] with k hk hg hs
  change ‖(|H| * 3^n)*(Real.log (β k))^n‖ ≤ δ*‖C.S.scale k‖ at hk
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg hs] at hk
  have hΛ : 0 ≤ Λ k := (lambda_pos C k).le
  change 1 ≤ Real.log (β k) at hg
  have triple : Λ k ≤ 3*Real.log (β k) := by change 2+_ ≤ _; linarith
  exact ((mul_le_mul (le_abs_self H) (pow_le_pow_left₀ hΛ triple _) (pow_nonneg hΛ _)
    (abs_nonneg H)).trans_eq (by rw [mul_pow]; ring)).trans hk

theorem polynomial (Y : Therm.Poetry C.path.levels) (v : ℕ → ℕ) (n : ℕ)
    {A : ℝ} (hA : 0 ≤ A) (shape : ∀ᶠ k in atTop, C.S.a (v k)/C.S.a k ≤ A*(Λ k)^n)
    {δ : ℝ} (hd : 0 < δ) :
    ∀ᶠ k in atTop, stakes C (v k) k ≤ Real.exp (δ*C.S.scale k) := by
  filter_upwards [shape,Vac.treasury_stage C.path.levels hG,small C hG (A^4) (n*4+2) (half_pos hd),
    (C.S.divergent.const_mul_atTop (half_pos hd)).eventually_ge_atTop 5] with k hk ht hs h5
  have hp := (Y.stage k).price
  have hlog := (Real.log_pos (C.path.levels.fits.delayed k)).le
  have hsq : (Real.log (β k))^2 ≤ (Λ k)^2 := by
    apply pow_le_pow_left₀ hlog
    change _ ≤ 2+_; linarith
  have hV : Vac.treasury C.path.levels k ≤ (Λ k)^2 :=
    (ht.trans (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) hp)).trans hsq
  have ratioPos := (div_pos (C.S.a_pos (v k)) (C.S.a_pos k)).le
  have power := mul_le_mul (pow_le_pow_left₀ ratioPos hk 4) (le_refl ((Λ k)^2))
    (sq_nonneg _) (pow_nonneg (mul_nonneg hA (pow_nonneg (lambda_pos C k).le _)) _)
  have bill : (C.S.a (v k)/C.S.a k)^4 * Vac.treasury C.path.levels k ≤ δ/2*C.S.scale k :=
    ((mul_le_mul_of_nonneg_left hV (pow_nonneg ratioPos _)).trans power).trans
      ((le_of_eq (by rw [mul_pow,← pow_mul,pow_add]; ring)).trans hs)
  apply Real.exp_le_exp.mpr
  linarith

theorem posted (Y : Therm.Poetry C.path.levels) {L B δ : ℝ} (hL : 0 < L) (hB : 0 < B)
    (pace : ∀ k, ((C.S.block k).val:ℝ) ≤ Real.log (Λ k)) (hd : 0 < δ) :
    ∀ᶠ k in atTop, stakes C (port C L B hL k) k ≤ Real.exp (δ*C.S.scale k) := by
  let n := Nat.ceil (B+1)
  apply polynomial C hG Y (port C L B hL) (n+2) hL.le _ hd
  filter_upwards [outer_bound C hG L B hL hB pace] with k hk
  apply hk.trans
  unfold Upper
  rw [pow_add,← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hL.le
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
    (one_le_two.trans (lambda_up C k).le) (Nat.le_ceil (B+1))

theorem opened {L B : ℝ} (hL : 0 < L) (hB : 4 ≤ B) :
    ∀ᶠ k in atTop, Stock.Tabs.opens C.path.levels 1 (port C L B hL k) k := by
  have hs : ∀ k, (C.path.levels.clock.coverSize k : ℝ) ≤ (Λ k)^2 := by
    intro k
    have h := (Nat.ceil_lt_add_one (sq_nonneg (Real.log (β k)))).le
    have hx := Real.log_pos (C.path.levels.fits.delayed k)
    apply h.trans
    change (Real.log (β k))^2+1 ≤ (2+Real.log (β k))^2
    linarith only [show 0 < 4*Real.log (β k) from by positivity]
  filter_upwards [inner_bound C hG L B hL,port_small C hG L B hL (by linarith),
    (lambda_leads C hG).eventually_ge_atTop L⁻¹] with k hi hk hΛ
  refine ⟨(Nat.le_succ _).trans hk.le,?_⟩
  rw [one_mul]
  have hpow : Λ k^4 ≤ L*Λ k^(B+1) := by
    have h1 : 1 ≤ L*Λ k := (inv_le_iff_one_le_mul₀' hL).mp hΛ
    have hmono := Real.rpow_le_rpow_of_exponent_le (one_le_two.trans (lambda_up C k).le)
      (show (5:ℝ) ≤ B+1 by linarith)
    calc
      _ ≤ (L*Λ k)*Λ k^4 := le_mul_of_one_le_left (pow_nonneg (lambda_pos C _).le _) h1
      _ = L*Λ k^(5:ℝ) := by rw [Real.rpow_ofNat]; ring
      _ ≤ L*Λ k^(B+1) := mul_le_mul_of_nonneg_left hmono hL.le
  have fit := (pow_le_pow_left₀ (Nat.cast_nonneg _) (hs k) 2).trans_eq (by ring : ((Λ k)^2)^2=(Λ k)^4)
  apply (fit.trans hpow).trans
  apply (le_div_iff₀ (C.S.a_pos k)).mpr
  exact hi.trans (C.S.strictAnti.antitone (Nat.le_succ _))

end YM.Integration.WilsonMovingReportTreasury
