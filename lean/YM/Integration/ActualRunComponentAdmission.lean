import YM.Integration.ActualRunAdmissionClock
import YM.Integration.FullQLocalStrongApplication

/-! Numerical Admission for the exact existential component widths. The
original Run must supply WidthPayment; positivity or an upper comparison to
stored widths does not supply that receipt. The calibration cap is an internal
parameter until the selected-output reset identifies the actual sequence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunComponentAdmission
open Filter Function Lattice RG FullQLocal
open ActualRunAdmissionScales
open scoped Topology

variable {G : Gauge}

def rate (C : Family G) (W : ProfileWidths) (m : ℕ) : ℝ :=
  W.pair C m / (W.pair C m + 2)

def cost (C : Family G) (W : ProfileWidths) (m : ℕ) : ℝ :=
  admittedCost C.path.levels m + 3*(W.pair C m)⁻¹

lemma rate_pos (C : Family G) (W : ProfileWidths) (m : ℕ) : 0 < rate C W m := by
  have hp := W.pair_positive C m
  unfold rate
  positivity

lemma rate_inv (C : Family G) (W : ProfileWidths) (m : ℕ) :
    (rate C W m)⁻¹ = 1+2*(W.pair C m)⁻¹ := by
  rw [rate, inv_div, add_div, div_self (W.pair_positive C m).ne', div_eq_mul_inv]

lemma rate_width (C : Family G) (W : ProfileWidths) (m : ℕ) :
    rate C W m ≤ W.pair C m/2 := by
  have hp := W.pair_positive C m
  unfold rate
  apply (div_le_iff₀ (show 0 < W.pair C m+2 by linarith)).mpr
  nlinarith [sq_nonneg (W.pair C m)]

lemma cost_ge_native (C : Family G) (W : ProfileWidths) (m : ℕ) :
    admittedCost C.path.levels m ≤ cost C W m := by
  have hp := inv_pos.mpr (W.pair_positive C m)
  unfold cost
  linarith

lemma cost_one (C : Family G) (W : ProfileWidths) (m : ℕ) : 1 ≤ cost C W m :=
  (admittedCost_one C.path.levels m).trans (cost_ge_native C W m)

lemma cost_width (C : Family G) (W : ProfileWidths) (m : ℕ) :
    (W.pair C m)⁻¹+(W.pair C m/2)⁻¹+1 ≤ cost C W m := by
  have hp := admittedCost_one C.path.levels m
  rw [inv_div, div_eq_mul_inv]
  unfold cost
  linarith

lemma rate_cost (C : Family G) (W : ProfileWidths) (m : ℕ) :
    (rate C W m)⁻¹ ≤ cost C W m := by
  have hp := admittedCost_one C.path.levels m
  have hw := inv_pos.mpr (W.pair_positive C m)
  rw [rate_inv]
  unfold cost
  linarith

/-- Exact fixed-polynomial reciprocal-width payment implies a rate larger
than every fixed inverse logarithmic scale. The payment is not assumed from
positive or stored-profile widths. -/
theorem rate_scale (C : Family G) (W : ProfileWidths) (P : WidthPayment C W)
    (hG : G.Simple) (D : ℝ) (hD : 0 < D) :
    ∀ᶠ m in atTop, D*(rate C W m)⁻¹ ≤ Real.log (C.path.levels.clock.hatBeta m) := by
  let A := C.path.levels
  let K : ℝ := D*(1+2*P.coefficient)
  have hz : Tendsto (widthScale C) atTop atTop := by
    change Tendsto (fun m => 1 + Next.Scheduling.Clock.tick (A.clock.hatBeta m))
      atTop atTop
    exact tendsto_const_nhds.add_atTop
      (Next.Scheduling.Clock.clock.comp (WardBin.bell A hG))
  have hsmall := ((isLittleO_rpow_exp_atTop (P.degree : ℝ)).const_mul_left K).bound
    (Real.exp_pos (-1))
  filter_upwards [hz.eventually hsmall, eventually_ge_atTop P.first] with m hm hfirst
  let z := widthScale C m
  have hz1 : 1 ≤ z := P.scale_ge_one m hfirst
  have hp1 : 1 ≤ z^P.degree := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hz1 P.degree
  have hrecip : (W.pair C m)⁻¹ ≤ P.coefficient*z^P.degree := P.reciprocal m hfirst
  have hbound : K*z^P.degree ≤ Real.exp (-1)*Real.exp z := by
    have h : |K*z^P.degree| ≤ Real.exp (-1)*|Real.exp z| := by
      simpa only [Real.norm_eq_abs, Real.rpow_natCast] using hm
    rw [abs_of_pos (Real.exp_pos z)] at h
    exact (le_abs_self _).trans h
  have hrate : D*(rate C W m)⁻¹ ≤ K*z^P.degree := by
    rw [rate_inv]
    have h := mul_le_mul_of_nonneg_left hrecip (show 0 ≤ 2*D by positivity)
    have h1 := mul_le_mul_of_nonneg_left hp1 hD.le
    dsimp [K]
    nlinarith
  have he : Real.exp (-1)*Real.exp z = Real.log (A.clock.hatBeta m) := by
    rw [← Real.exp_add]
    change Real.exp (-1+(1+Real.log (Real.log (A.clock.hatBeta m)))) = _
    rw [show (-1 : ℝ)+(1+Real.log (Real.log (A.clock.hatBeta m))) =
      Real.log (Real.log (A.clock.hatBeta m)) by ring]
    exact Real.exp_log (Real.log_pos (A.fits.delayed m))
  exact hrate.trans (hbound.trans_eq he)

lemma regular_exponent (C : Family G) (W : ProfileWidths) (P : WidthPayment C W)
    (hG : G.Simple) (D : ℝ) (hD : 0 < D) :
    ∀ᶠ m in atTop, D*Real.log (C.path.levels.clock.hatBeta m) ≤
      rate C W m*(C.path.levels.clock.coverSize m : ℝ) := by
  let A := C.path.levels
  filter_upwards [rate_scale C W P hG D hD] with m hm
  have hr := rate_pos C W m
  have hz := Real.log_pos (A.fits.delayed m)
  have hb : D ≤ Real.log (A.clock.hatBeta m)*rate C W m :=
    (div_le_iff₀ hr).mp (by simpa only [div_eq_mul_inv] using hm)
  have hc : (Real.log (A.clock.hatBeta m))^2 ≤ (A.clock.coverSize m : ℝ) := Nat.le_ceil _
  have hc' := mul_le_mul_of_nonneg_left hc hr.le
  nlinarith [mul_le_mul_of_nonneg_right hb hz.le]

lemma forced_exponent (C : Family G) (W : ProfileWidths) (P : WidthPayment C W)
    (hG : G.Simple) (δ D : ℝ) (hδ : 0 < δ) (hD : 0 < D) (d : ℕ) :
    ∀ᶠ m in atTop, D*Real.log (C.path.levels.clock.hatBeta m) ≤
      rate C W m*(C.path.levels.clock.monitor m)^δ /
        (1+(C.path.levels.clock.coverSize m : ℝ))^d := by
  let A := C.path.levels
  have ht := ((Next.Scheduling.Clock.ceiling_cheaper 2 δ (d+2)
    (by norm_num) hδ).comp (WardBin.bell A hG)).const_mul D
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const zero_lt_one, rate_scale C W P hG 1 zero_lt_one,
    (Real.tendsto_log_atTop.comp (WardBin.bell A hG)).eventually_ge_atTop 1] with m hp hr hz
  let v : ℝ := 1+(A.clock.coverSize m : ℝ)
  have hv : 0 < v := by dsimp [v]; positivity
  have hM : 0 < (A.clock.monitor m)^δ := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hp' : D*v^(d+2) ≤ (A.clock.monitor m)^δ := by
    have hq : D*(v^(d+2)/(A.clock.monitor m)^δ) ≤ 1 := by
      simpa only [Function.comp_apply, Next.Scheduling.Clock.watch_two,
        Next.Scheduling.Clock.cover, Next.Scheduling.Clock.tick,
        Calendar.coverSize, Calendar.monitor, v] using hp
    have hdiv : (D*v^(d+2))/(A.clock.monitor m)^δ ≤ 1 := by
      rw [mul_div_assoc]
      exact hq
    have he : D*v^(d+2) ≤ 1*(A.clock.monitor m)^δ :=
      (div_le_iff₀ hM).mp hdiv
    simpa only [one_mul] using he
  have hc : (Real.log (A.clock.hatBeta m))^2 ≤ (A.clock.coverSize m : ℝ) := Nat.le_ceil _
  have hzv : Real.log (A.clock.hatBeta m) ≤ v := by dsimp [v]; nlinarith
  have hir : (rate C W m)⁻¹ ≤ v := by
    have hri : (rate C W m)⁻¹ ≤ Real.log (A.clock.hatBeta m) := by
      simpa only [one_mul] using hr
    exact hri.trans hzv
  have hproduct : D*Real.log (A.clock.hatBeta m)*v^d*(rate C W m)⁻¹ ≤ D*v^(d+2) := by
    calc
      _ ≤ (D*v*v^d)*v := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzv hD.le)
          (pow_nonneg hv.le _)) hir (inv_nonneg.mpr (rate_pos C W m).le) (by positivity)
      _ = _ := by rw [pow_add, pow_two]; ring
  have hpay : D*Real.log (A.clock.hatBeta m)*v^d ≤ (A.clock.monitor m)^δ*rate C W m :=
    (div_le_iff₀ (rate_pos C W m)).mp
      (by simpa only [div_eq_mul_inv] using hproduct.trans hp')
  change D*Real.log (A.clock.hatBeta m) ≤ rate C W m*(A.clock.monitor m)^δ/v^d
  exact (le_div_iff₀ (pow_pos hv _)).mpr (by simpa only [mul_comm] using hpay)

lemma cost_monitor (C : Family G) (W : ProfileWidths) (P : WidthPayment C W)
    (hG : G.Simple) (hMesh : ActualRunAdmissionClock.PreMesh C.path.levels) :
    ∀ᶠ m in atTop, cost C W m ≤ 28*C.path.levels.clock.monitor (m+1) := by
  let A := C.path.levels
  filter_upwards [ActualRunAdmissionClock.cost_monitor A hG hMesh,
    rate_scale C W P hG 1 zero_lt_one,
    (tendsto_add_atTop_nat 1).eventually (ActualRunAdmissionClock.cover_monitor A hG),
    (Real.tendsto_log_atTop.comp (WardBin.bell A hG)).eventually_ge_atTop 1] with m hc hr hcover hz
  have hmono : (A.clock.coverSize m : ℝ) ≤ (A.clock.coverSize (m+1) : ℝ) := by
    exact_mod_cast ActualRunAdmissionClock.cover_next A hG m
  have hsq : (Real.log (A.clock.hatBeta m))^2 ≤ (A.clock.coverSize m : ℝ) := Nat.le_ceil _
  rw [one_mul, rate_inv] at hr
  have hw : (W.pair C m)⁻¹ ≤ A.clock.monitor (m+1) := by nlinarith
  unfold cost
  linarith

lemma cost_hat_tendsto (C : Family G) (W : ProfileWidths) (P : WidthPayment C W)
    (hG : G.Simple) (hMesh : ActualRunAdmissionClock.PreMesh C.path.levels)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m => cost C W m*C.path.levels.clock.hatCoupling (m+1)^ε) atTop (𝓝 0) := by
  let A := C.path.levels
  have ht := ((LocalComparison.JetNormalization.monitor_hat_tendsto A hG 1 ε hε).comp
    (tendsto_add_atTop_nat 1)).const_mul 28
  simp only [mul_zero, pow_one, Function.comp_def] at ht
  apply squeeze_zero' (Eventually.of_forall fun m => mul_nonneg
    (zero_le_one.trans (cost_one C W m))
    (Real.rpow_nonneg (WardBin.stepG A (m+1)).le ε)) ?_ ht
  filter_upwards [cost_monitor C W P hG hMesh] with m hm
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hm
    (Real.rpow_nonneg (WardBin.stepG A (m+1)).le ε)

theorem cost_subpower (C : Family G) (W : ProfileWidths) (P : WidthPayment C W)
    (hG : G.Simple) (hC : C.Makes) (hMesh : ActualRunAdmissionClock.PreMesh C.path.levels)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ N period : ℕ, m < N → cost C W m ≤
      (Pert.Asymptotics.regulatorRun C N period (m+1))^(-ε) := by
  let A := C.path.levels
  have ht := (cost_hat_tendsto C W P hG hMesh ε hε).const_mul ((2 : ℝ)^ε)
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const zero_lt_one] with m hm N period hN
  let g := Pert.Asymptotics.regulatorRun C N period (m+1)
  have hg : 0 < g := IterationFour.Currency.g_pos hC N period (m+1) (by omega)
  have hgain := (IterationFour.Currency.hat_g hC N period (m+1) (by omega)).2
  have hgp : g^ε ≤ (2 : ℝ)^ε*A.clock.hatCoupling (m+1)^ε := by
    calc
      _ ≤ (2*A.clock.hatCoupling (m+1))^ε := Real.rpow_le_rpow hg.le hgain hε.le
      _ = _ := Real.mul_rpow (by norm_num) (WardBin.stepG A (m+1)).le
  have hpaid : cost C W m*g^ε ≤ 1 := by
    calc
      _ ≤ cost C W m*((2 : ℝ)^ε*A.clock.hatCoupling (m+1)^ε) :=
        mul_le_mul_of_nonneg_left hgp (zero_le_one.trans (cost_one C W m))
      _ = (2 : ℝ)^ε*(cost C W m*A.clock.hatCoupling (m+1)^ε) := by ring
      _ ≤ 1 := hm
  change cost C W m ≤ g^(-ε)
  rw [Real.rpow_neg hg.le, ← one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hg ε)).mpr hpaid

theorem regular_flat (C : Family G) (W : ProfileWidths) (P : WidthPayment C W)
    (hG : G.Simple) (hC : C.Makes) (hMesh : ActualRunAdmissionClock.PreMesh C.path.levels)
    (a c t : ℕ) :
    ∀ᶠ m in atTop, ∀ N period : ℕ, m < N →
      cost C W m^a*(Pert.Asymptotics.regulatorRun C N period (m+1))^(-(c : ℝ))*
        Real.exp (-rate C W m*(C.path.levels.clock.coverSize m : ℝ)) ≤
      (Pert.Asymptotics.regulatorRun C N period (m+1))^t := by
  let A := C.path.levels
  filter_upwards [cost_subpower C W P hG hC hMesh 1 zero_lt_one,
    ActualRunAdmissionClock.actual_inverse_lower C hG hC hMesh,
    regular_exponent C W P hG (((a+c+t : ℕ) : ℝ)+1) (by positivity)] with m hc hg he N period hN
  have hpos := IterationFour.Currency.g_pos hC N period (m+1) (by omega)
  have hc' : cost C W m ≤ (Pert.Asymptotics.regulatorRun C N period (m+1))⁻¹ := by
    simpa only [Real.rpow_neg_one] using hc N period hN
  have he' : ((a+c+t : ℕ) : ℝ)*Real.log (A.clock.hatBeta m) ≤
      rate C W m*(A.clock.coverSize m : ℝ) := by
    have hz := Real.log_pos (A.fits.delayed m)
    nlinarith
  simpa only [neg_mul] using ActualRunAdmissionClock.flat_product (WardBin.hot A m) hpos
    (zero_le_one.trans (cost_one C W m)) hc' (hg N period hN) a c t he'

theorem forced_flat (C : Family G) (W : ProfileWidths) (P : WidthPayment C W)
    (hG : G.Simple) (hC : C.Makes) (hMesh : ActualRunAdmissionClock.PreMesh C.path.levels)
    (δ : ℝ) (hδ : 0 < δ) (a c d t : ℕ) :
    ∀ᶠ m in atTop, ∀ N period : ℕ, m < N →
      cost C W m^a*(Pert.Asymptotics.regulatorRun C N period (m+1))^(-(c : ℝ))*
        Real.exp (-rate C W m*(C.path.levels.clock.monitor m)^δ /
          (1+(C.path.levels.clock.coverSize m : ℝ))^d) ≤
      (Pert.Asymptotics.regulatorRun C N period (m+1))^t := by
  let A := C.path.levels
  filter_upwards [cost_subpower C W P hG hC hMesh 1 zero_lt_one,
    ActualRunAdmissionClock.actual_inverse_lower C hG hC hMesh,
    forced_exponent C W P hG δ (((a+c+t : ℕ) : ℝ)+1) hδ (by positivity) d] with m hc hg he N period hN
  have hpos := IterationFour.Currency.g_pos hC N period (m+1) (by omega)
  have hc' : cost C W m ≤ (Pert.Asymptotics.regulatorRun C N period (m+1))⁻¹ := by
    simpa only [Real.rpow_neg_one] using hc N period hN
  have he' : ((a+c+t : ℕ) : ℝ)*Real.log (A.clock.hatBeta m) ≤
      rate C W m*(A.clock.monitor m)^δ/(1+(A.clock.coverSize m : ℝ))^d := by
    have hz := Real.log_pos (A.fits.delayed m)
    nlinarith
  simpa only [neg_div, neg_mul] using ActualRunAdmissionClock.flat_product (WardBin.hot A m) hpos
    (zero_le_one.trans (cost_one C W m)) hc' (hg N period hN) a c t he'

end YM.Integration.ActualRunComponentAdmission
end
