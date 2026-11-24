import YM.Integration.ActualRunAdmissionScales
import YM.Integration.RG05Preconstruction.Resources

/-! Scalar clock estimates for the full-qlocal Admission on the original
trajectory. PreMesh below is exactly the retained ReadoutPurchase field.
The final Run adapter must supply that existing receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunAdmissionClock
open Filter Function Lattice RG
open ActualRunAdmissionScales
open scoped Topology

variable {G : Gauge}

def slow (A : Levels G) (m : ℕ) : ℝ :=
  1 + Real.log (2 + Real.log (A.clock.hatBeta m))

def PreMesh (A : Levels G) : Prop :=
  ∀ m, ((A.S.block m).val : ℝ) ≤ slow A m

def envelope (A : Levels G) (m : ℕ) : ℝ := profileCost A 0 + slow A m

lemma slow_one (A : Levels G) (m : ℕ) : 1 ≤ slow A m := by
  have h := Real.log_pos (A.fits.delayed m)
  have hl := Real.log_nonneg (show 1 ≤ 2 + Real.log (A.clock.hatBeta m) by linarith)
  unfold slow
  linarith

lemma slow_mono (A : Levels G) (hG : G.Simple) : Monotone (slow A) := by
  intro i j hij
  have hb := Push.Corrected.Last.band_le A hG hij
  have hl := Real.log_le_log (WardBin.hot A i) hb
  have hinner : 0 < 2 + Real.log (A.clock.hatBeta i) := by
    have := Real.log_pos (A.fits.delayed i)
    linarith
  exact add_le_add (le_refl (1 : ℝ))
    (Real.log_le_log hinner (add_le_add (le_refl (2 : ℝ)) hl))

lemma profile_fine (A : Levels G) (hMesh : PreMesh A) (m : ℕ) :
    profileCost A (m+1) ≤ slow A m :=
  (profileCost_le_block A m).trans (hMesh m)

lemma profile_coarse (A : Levels G) (hG : G.Simple) (hMesh : PreMesh A) (m : ℕ) :
    profileCost A m ≤ envelope A m := by
  have h0 := profileCost_one A 0
  have hs := slow_one A m
  cases m with
  | zero => unfold envelope; linarith
  | succ k =>
    have h := (profile_fine A hMesh k).trans (slow_mono A hG (Nat.le_succ k))
    unfold envelope
    linarith

lemma profile_fine_envelope (A : Levels G) (hMesh : PreMesh A) (m : ℕ) :
    profileCost A (m+1) ≤ envelope A m := by
  have h := profile_fine A hMesh m
  have h0 := profileCost_one A 0
  unfold envelope
  linarith

lemma pair_inverse (A : Levels G) (hG : G.Simple) (hMesh : PreMesh A) (m : ℕ) :
    (pairWidth A m)⁻¹ ≤ envelope A m := by
  have hf := (profileCost_components A (m+1)).1.trans (profile_fine_envelope A hMesh m)
  have hc := (profileCost_components A m).1.trans (profile_coarse A hG hMesh m)
  rcases le_total (A.params (m+1)).width (A.params m).width with h | h
  · simpa only [pairWidth, min_eq_left h] using hf
  · simpa only [pairWidth, min_eq_right h] using hc

lemma rate_inverse (A : Levels G) (hG : G.Simple) (hMesh : PreMesh A) (m : ℕ) :
    (pathRate A m)⁻¹ ≤ 1 + 2 * envelope A m := by
  rw [pathRate_inv]
  exact add_le_add (le_refl (1 : ℝ))
    (mul_le_mul_of_nonneg_left (pair_inverse A hG hMesh m)
      (show (0 : ℝ) ≤ 2 by norm_num))

/-- The preMesh width price is smaller than every fixed multiple of log beta.
This supplies the moving-width support tail; bare subpower cost would not. -/
theorem rate_scale (A : Levels G) (hG : G.Simple) (D : ℝ) (_hD : 0 < D) :
    ∀ᶠ m in atTop, D * (1 + 2 * envelope A m) ≤ Real.log (A.clock.hatBeta m) := by
  have hz := Real.tendsto_log_atTop.comp (WardBin.bell A hG)
  have hx : Tendsto (fun m => 2 + Real.log (A.clock.hatBeta m)) atTop atTop :=
    tendsto_const_nhds.add_atTop hz
  have hsmall := (Real.isLittleO_log_id_atTop.const_mul_left (2*D)).bound
    (show 0 < (1/4 : ℝ) by norm_num)
  filter_upwards [hx.eventually hsmall, hz.eventually_ge_atTop 2,
    hz.eventually_ge_atTop (2*D*(3+2*profileCost A 0))] with m hm hz2 hconst
  change 2 ≤ Real.log (A.clock.hatBeta m) at hz2
  change 2*D*(3+2*profileCost A 0) ≤ Real.log (A.clock.hatBeta m) at hconst
  have hlog : 2*D*Real.log (2+Real.log (A.clock.hatBeta m)) ≤
      (1/4 : ℝ)*(2+Real.log (A.clock.hatBeta m)) := by
    have hh : |2*D*Real.log (2+Real.log (A.clock.hatBeta m))| ≤
        (1/4 : ℝ)*|2+Real.log (A.clock.hatBeta m)| := by
      simpa only [Real.norm_eq_abs, id_eq] using hm
    rw [abs_of_pos (show 0 < 2+Real.log (A.clock.hatBeta m) by linarith)] at hh
    exact (le_abs_self _).trans hh
  unfold envelope slow
  nlinarith

lemma regular_exponent (A : Levels G) (hG : G.Simple) (hMesh : PreMesh A)
    (D : ℝ) (hD : 0 < D) :
    ∀ᶠ m in atTop, D*Real.log (A.clock.hatBeta m) ≤
      pathRate A m * (A.clock.coverSize m : ℝ) := by
  filter_upwards [rate_scale A hG D hD] with m hm
  have hr := pathRate_pos A m
  have hz := Real.log_pos (A.fits.delayed m)
  have hi : D*(pathRate A m)⁻¹ ≤ Real.log (A.clock.hatBeta m) :=
    (mul_le_mul_of_nonneg_left (rate_inverse A hG hMesh m) hD.le).trans hm
  have hbase : D ≤ Real.log (A.clock.hatBeta m)*pathRate A m :=
    (div_le_iff₀ hr).mp (by simpa only [div_eq_mul_inv] using hi)
  have hc : (Real.log (A.clock.hatBeta m))^2 ≤ (A.clock.coverSize m : ℝ) :=
    Nat.le_ceil _
  have hc' := mul_le_mul_of_nonneg_left hc hr.le
  nlinarith [mul_le_mul_of_nonneg_right hbase hz.le]

lemma forced_exponent (A : Levels G) (hG : G.Simple) (hMesh : PreMesh A)
    (δ D : ℝ) (hδ : 0 < δ) (hD : 0 < D) (d : ℕ) :
    ∀ᶠ m in atTop, D*Real.log (A.clock.hatBeta m) ≤
      pathRate A m * (A.clock.monitor m)^δ /
        (1+(A.clock.coverSize m : ℝ))^d := by
  have ht := ((Next.Scheduling.Clock.ceiling_cheaper 2 δ (d+2)
    (by norm_num) hδ).comp (WardBin.bell A hG)).const_mul D
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const zero_lt_one,
    rate_scale A hG 1 zero_lt_one,
    (Real.tendsto_log_atTop.comp (WardBin.bell A hG)).eventually_ge_atTop 1] with m hp hr hz
  let v : ℝ := 1+(A.clock.coverSize m : ℝ)
  have hv : 0 < v := by dsimp [v]; positivity
  have hM : 0 < (A.clock.monitor m)^δ :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
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
  have hir : (pathRate A m)⁻¹ ≤ v := by
    have h := (rate_inverse A hG hMesh m).trans (by simpa only [one_mul] using hr)
    exact h.trans hzv
  have hproduct : D*Real.log (A.clock.hatBeta m)*v^d*(pathRate A m)⁻¹ ≤
      D*v^(d+2) := by
    calc
      _ ≤ (D*v*v^d)*v := mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzv hD.le)
          (pow_nonneg hv.le _)) hir
        (inv_nonneg.mpr (pathRate_pos A m).le)
        (by positivity)
      _ = _ := by rw [pow_add, pow_two]; ring
  have hpay : D*Real.log (A.clock.hatBeta m)*v^d ≤
      (A.clock.monitor m)^δ*pathRate A m :=
    (div_le_iff₀ (pathRate_pos A m)).mp
      (by simpa only [div_eq_mul_inv] using hproduct.trans hp')
  change D*Real.log (A.clock.hatBeta m) ≤ pathRate A m*(A.clock.monitor m)^δ/v^d
  exact (le_div_iff₀ (pow_pos hv _)).mpr (by simpa only [mul_comm] using hpay)

/-- Adjacent temperatures use the actual schedule recursion and preMesh. -/
lemma adjacent_beta (A : Levels G) (hG : G.Simple) (hMesh : PreMesh A) :
    ∀ᶠ m in atTop, A.clock.hatBeta (m+1) ≤ 2*A.clock.hatBeta m := by
  let s := G.slopeConstant
  have hs : 0 < s := G.slopeConstant_pos hG
  have hsmall := (Real.isLittleO_log_id_atTop.const_mul_left (s+1)).bound
    (show 0 < (1/2 : ℝ) by norm_num)
  filter_upwards [(WardBin.bell A hG).eventually hsmall,
    (WardBin.bell A hG).eventually_ge_atTop 4] with m hm h4
  have hb := WardBin.hot A m
  have hz := Real.log_pos (A.fits.delayed m)
  have hpaid : (s+1)*Real.log (A.clock.hatBeta m) ≤ A.clock.hatBeta m/2 := by
    have h : |(s+1)*Real.log (A.clock.hatBeta m)| ≤
        (1/2 : ℝ)*|A.clock.hatBeta m| := by
      simpa only [Real.norm_eq_abs, id_eq] using hm
    rw [abs_of_pos hb] at h
    have hl := (le_abs_self ((s+1)*Real.log (A.clock.hatBeta m))).trans h
    linarith
  have hzsmall : Real.log (A.clock.hatBeta m) ≤ A.clock.hatBeta m/2 := by
    nlinarith
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < 2+Real.log (A.clock.hatBeta m) by linarith)
  have hL : 0 < ((A.S.block m).val : ℝ) := by exact_mod_cast (A.S.block m).property
  have hLb : ((A.S.block m).val : ℝ) ≤ A.clock.hatBeta m := by
    have h := hMesh m
    unfold slow at h
    linarith
  have hgain : s*Real.log ((A.S.block m).val : ℝ) ≤ A.clock.hatBeta m/2 := by
    have h := mul_le_mul_of_nonneg_left (Real.log_le_log hL hLb) hs.le
    nlinarith
  have he : A.clock.hatBeta (m+1) = A.clock.hatBeta m +
      s*Real.log ((A.S.block m).val : ℝ) := by
    unfold Calendar.hatBeta
    rw [Schedule.scale_succ]
    dsimp only [s]
    ring
  linarith

lemma adjacent_hat (A : Levels G) (hG : G.Simple) (hMesh : PreMesh A) :
    ∀ᶠ m in atTop, A.clock.hatCoupling m ≤ 2*A.clock.hatCoupling (m+1) := by
  filter_upwards [adjacent_beta A hG hMesh] with m hm
  have hmono := Push.Corrected.Last.band_le A hG (Nat.le_succ m)
  have hb := WardBin.hot A m
  have hstripe : A.clock.hatBeta (m+1) ∈
      IterationFour.Currency.stripe (A.clock.hatBeta m) := by
    constructor <;> linarith
  exact (IterationFour.Currency.sizes_band hb hstripe).1

lemma monitor_one (A : Levels G) (m : ℕ) : 1 ≤ A.clock.monitor m :=
  Real.one_le_exp (sq_nonneg _)

lemma cover_next (A : Levels G) (hG : G.Simple) (m : ℕ) :
    A.clock.coverSize m ≤ A.clock.coverSize (m+1) := by
  have hl := Real.log_le_log (WardBin.hot A m)
    (Push.Corrected.Last.band_le A hG (Nat.le_succ m))
  exact Nat.ceil_mono (pow_le_pow_left₀ (Real.log_pos (A.fits.delayed m)).le hl 2)

lemma monitor_next (A : Levels G) (hG : G.Simple) (m : ℕ)
    (hm : 1 ≤ Real.log (A.clock.hatBeta m)) :
    A.clock.monitor m ≤ A.clock.monitor (m+1) := by
  have hl := Real.log_le_log (WardBin.hot A m)
    (Push.Corrected.Last.band_le A hG (Nat.le_succ m))
  have ht := Real.log_le_log (Real.log_pos (A.fits.delayed m)) hl
  exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (Real.log_nonneg hm) ht 2)

lemma loop_le (A : Levels G) (m : ℕ) :
    A.clock.loopCap m ≤ 2*A.clock.monitor m := by
  have hj : (1 : ℝ) ≤ (A.clock.J m : ℝ) := by
    exact_mod_cast (show 1 ≤ A.clock.J m from (by decide : 1 ≤ 4).trans (A.clock.adm m))
  have hi : (A.clock.J m : ℝ)⁻¹ ≤ 1 := by
    simpa only [inv_one] using inv_anti₀ zero_lt_one hj
  have ht := (A.fits.thetaRange m).2.trans hi
  have hp := Real.rpow_le_rpow_of_exponent_le (monitor_one A m) ht
  simpa only [Calendar.loopCap, Real.rpow_one] using
    mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)

lemma cover_monitor (A : Levels G) (hG : G.Simple) :
    ∀ᶠ m in atTop, 1+(A.clock.coverSize m : ℝ) ≤ A.clock.monitor m := by
  have ht := (Next.Scheduling.Clock.ceiling_cheaper 2 1 1
    (by norm_num) zero_lt_one).comp (WardBin.bell A hG)
  filter_upwards [ht.eventually_le_const zero_lt_one] with m hm
  have h : (1+(A.clock.coverSize m : ℝ))/A.clock.monitor m ≤ 1 := by
    simpa only [Function.comp_apply, Next.Scheduling.Clock.watch_two,
      Next.Scheduling.Clock.cover, Next.Scheduling.Clock.tick,
      Calendar.coverSize, Calendar.monitor, Real.rpow_one, pow_one] using hm
  simpa only [one_mul] using (div_le_iff₀ (show 0 < A.clock.monitor m from Real.exp_pos _)).mp h

/-- All listed geometry and unit costs are paid by the actual next monitor.
The constant is fixed; the late event retains the original initial profile. -/
theorem cost_monitor (A : Levels G) (hG : G.Simple) (hMesh : PreMesh A) :
    ∀ᶠ m in atTop, admittedCost A m ≤ 25*A.clock.monitor (m+1) := by
  filter_upwards [adjacent_hat A hG hMesh,
    (tendsto_add_atTop_nat 1).eventually (cover_monitor A hG),
    rate_scale A hG 1 zero_lt_one,
    (Real.tendsto_log_atTop.comp (WardBin.bell A hG)).eventually_ge_atTop 1] with m hh hc hr hz
  have hmono := monitor_next A hG m hz
  have hcover : (A.clock.coverSize m : ℝ) ≤ (A.clock.coverSize (m+1) : ℝ) := by
    exact_mod_cast cover_next A hG m
  have hsq : (Real.log (A.clock.hatBeta m))^2 ≤ (A.clock.coverSize m : ℝ) := Nat.le_ceil _
  have he : envelope A m ≤ A.clock.monitor (m+1) := by
    simp only [one_mul] at hr
    nlinarith
  have hw := (pair_inverse A hG hMesh m).trans he
  have hpc := (profile_coarse A hG hMesh m).trans he
  have hpf := (profile_fine_envelope A hMesh m).trans he
  have hcc := profileCost_components A m
  have hcf := profileCost_components A (m+1)
  have hlc := (loop_le A m).trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
  have hlf := loop_le A (m+1)
  have hgeo : geometryCost A m ≤ 1+14*A.clock.monitor (m+1) := by
    unfold geometryCost
    linarith [hcc.2.1.trans hpc, hcc.2.2.1.trans hpc, hcc.2.2.2.trans hpc,
      hcf.2.1.trans hpf, hcf.2.2.1.trans hpf, hcf.2.2.2.trans hpf]
  have hu : unitCost A m ≤ 6*A.clock.monitor (m+1) := by
    have hg := WardBin.stepG A (m+1)
    have hm0 : 0 ≤ A.clock.monitor m := (Real.exp_pos _).le
    have hterm := mul_le_mul hh hmono hm0 (by positivity : 0 ≤ 2*A.clock.hatCoupling (m+1))
    unfold unitCost Calendar.threshold
    apply (div_le_iff₀ hg).mpr
    nlinarith
  have hM := monitor_one A (m+1)
  unfold admittedCost
  linarith

lemma cost_hat_tendsto (A : Levels G) (hG : G.Simple) (hMesh : PreMesh A)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m => admittedCost A m * A.clock.hatCoupling (m+1)^ε)
      atTop (𝓝 0) := by
  have ht := ((LocalComparison.JetNormalization.monitor_hat_tendsto A hG 1 ε hε).comp
    (tendsto_add_atTop_nat 1)).const_mul 25
  simp only [mul_zero, pow_one, Function.comp_def] at ht
  apply squeeze_zero' (Eventually.of_forall fun m => mul_nonneg
    (zero_le_one.trans (admittedCost_one A m))
    (Real.rpow_nonneg (WardBin.stepG A (m+1)).le ε)) ?_ ht
  filter_upwards [cost_monitor A hG hMesh] with m hm
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hm
    (Real.rpow_nonneg (WardBin.stepG A (m+1)).le ε)

/-- One event precedes every cutoff and period on the same family. -/
theorem cost_subpower (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (hMesh : PreMesh C.path.levels) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ N period : ℕ, m < N →
      admittedCost C.path.levels m ≤
        (Pert.Asymptotics.regulatorRun C N period (m+1))^(-ε) := by
  let A := C.path.levels
  have ht := (cost_hat_tendsto A hG hMesh ε hε).const_mul ((2 : ℝ)^ε)
  rw [mul_zero] at ht
  filter_upwards [ht.eventually_le_const zero_lt_one] with m hm N period hN
  let g := Pert.Asymptotics.regulatorRun C N period (m+1)
  have hg : 0 < g := IterationFour.Currency.g_pos hC N period (m+1) (by omega)
  have hgain := (IterationFour.Currency.hat_g hC N period (m+1) (by omega)).2
  have hgp : g^ε ≤ (2 : ℝ)^ε * A.clock.hatCoupling (m+1)^ε := by
    calc
      _ ≤ (2*A.clock.hatCoupling (m+1))^ε := Real.rpow_le_rpow hg.le hgain hε.le
      _ = _ := Real.mul_rpow (by norm_num) (WardBin.stepG A (m+1)).le
  have hpaid : admittedCost A m * g^ε ≤ 1 := by
    calc
      _ ≤ admittedCost A m * ((2 : ℝ)^ε * A.clock.hatCoupling (m+1)^ε) :=
        mul_le_mul_of_nonneg_left hgp (zero_le_one.trans (admittedCost_one A m))
      _ = (2 : ℝ)^ε * (admittedCost A m * A.clock.hatCoupling (m+1)^ε) := by ring
      _ ≤ 1 := hm
  change admittedCost A m ≤ g^(-ε)
  rw [Real.rpow_neg hg.le, ← one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hg ε)).mpr hpaid

lemma actual_inverse_lower (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (hMesh : PreMesh C.path.levels) :
    ∀ᶠ m in atTop, ∀ N period : ℕ, m < N →
      (C.path.levels.clock.hatBeta m)⁻¹ ≤
        Pert.Asymptotics.regulatorRun C N period (m+1) := by
  let A := C.path.levels
  filter_upwards [adjacent_hat A hG hMesh,
    (WardBin.bell A hG).eventually_ge_atTop 16] with m hm hb16 N period hN
  have hb := WardBin.hot A m
  have hs := Real.sqrt_pos.mpr hb
  have hs4 : 4 ≤ Real.sqrt (A.clock.hatBeta m) :=
    Real.le_sqrt_of_sq_le (by norm_num; exact hb16)
  have hsq := Real.sq_sqrt hb.le
  have h4 : 4*Real.sqrt (A.clock.hatBeta m) ≤ A.clock.hatBeta m := by nlinarith
  have hi := inv_anti₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hs) h4
  have hib : (A.clock.hatBeta m)⁻¹ ≤ A.clock.hatCoupling m/4 := by
    simpa only [Calendar.hatCoupling, mul_inv_rev, div_eq_mul_inv] using hi
  have hh := (IterationFour.Currency.hat_g hC N period (m+1) (by omega)).1
  change A.clock.hatCoupling (m+1) ≤
    2*Pert.Asymptotics.regulatorRun C N period (m+1) at hh
  linarith

lemma flat_product {b g C r : ℝ} (hb : 0 < b) (hg : 0 < g)
    (hC0 : 0 ≤ C) (hC : C ≤ g⁻¹) (hbg : b⁻¹ ≤ g)
    (a c t : ℕ) (he : ((a+c+t : ℕ) : ℝ)*Real.log b ≤ r) :
    C^a * g^(-(c : ℝ)) * Real.exp (-r) ≤ g^t := by
  let n := a+c+t
  have hidentity : (b⁻¹)^n = Real.exp (-(n : ℝ)*Real.log b) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (inv_pos.mpr hb), Real.log_inv]
    congr 1
    ring
  have hexp : Real.exp (-r) ≤ g^n := by
    calc
      _ ≤ Real.exp (-(n : ℝ)*Real.log b) := Real.exp_le_exp.mpr (by dsimp [n]; linarith)
      _ = (b⁻¹)^n := hidentity.symm
      _ ≤ g^n := pow_le_pow_left₀ (inv_nonneg.mpr hb.le) hbg n
  calc
    _ ≤ ((g⁻¹)^a * g^(-(c : ℝ))) * g^n := mul_le_mul
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC0 hC a)
        (Real.rpow_nonneg hg.le _)) hexp (Real.exp_pos _).le (by positivity)
    _ = g^t := by
      have hi : (g⁻¹)^a = g^(-(a : ℝ)) := by
        simp only [Real.rpow_neg hg.le, Real.rpow_natCast, inv_pow]
      rw [hi, ← Real.rpow_natCast, ← Real.rpow_add hg, ← Real.rpow_add hg]
      have hn : -(a : ℝ) + -(c : ℝ) + (n : ℝ) = (t : ℝ) := by dsimp [n]; push_cast; ring
      rw [hn, Real.rpow_natCast]

/-- The original support tail pays every requested fixed polynomial price. -/
theorem regular_flat (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (hMesh : PreMesh C.path.levels) (a c t : ℕ) :
    ∀ᶠ m in atTop, ∀ N period : ℕ, m < N →
      admittedCost C.path.levels m^a *
        (Pert.Asymptotics.regulatorRun C N period (m+1))^(-(c : ℝ)) *
        Real.exp (-pathRate C.path.levels m * (C.path.levels.clock.coverSize m : ℝ)) ≤
      (Pert.Asymptotics.regulatorRun C N period (m+1))^t := by
  let A := C.path.levels
  filter_upwards [cost_subpower C hG hC hMesh 1 zero_lt_one,
    actual_inverse_lower C hG hC hMesh,
    regular_exponent A hG hMesh (((a+c+t : ℕ) : ℝ)+1) (by positivity)] with m hc hg he N period hN
  have hpos := IterationFour.Currency.g_pos hC N period (m+1) (by omega)
  have hc' : admittedCost A m ≤ (Pert.Asymptotics.regulatorRun C N period (m+1))⁻¹ := by
    simpa only [Real.rpow_neg_one] using hc N period hN
  have he' : ((a+c+t : ℕ) : ℝ)*Real.log (A.clock.hatBeta m) ≤
      pathRate A m*(A.clock.coverSize m : ℝ) := by
    have hz := Real.log_pos (A.fits.delayed m)
    nlinarith
  simpa only [neg_mul] using flat_product (WardBin.hot A m) hpos
    (zero_le_one.trans (admittedCost_one A m)) hc' (hg N period hN) a c t he'

/-- The original forced tail keeps its full denominator power and any
positive monitor exponent. No width or clock is replaced. -/
theorem forced_flat (C : Family G) (hG : G.Simple) (hC : C.Makes)
    (hMesh : PreMesh C.path.levels) (δ : ℝ) (hδ : 0 < δ) (a c d t : ℕ) :
    ∀ᶠ m in atTop, ∀ N period : ℕ, m < N →
      admittedCost C.path.levels m^a *
        (Pert.Asymptotics.regulatorRun C N period (m+1))^(-(c : ℝ)) *
        Real.exp (-pathRate C.path.levels m * (C.path.levels.clock.monitor m)^δ /
          (1+(C.path.levels.clock.coverSize m : ℝ))^d) ≤
      (Pert.Asymptotics.regulatorRun C N period (m+1))^t := by
  let A := C.path.levels
  filter_upwards [cost_subpower C hG hC hMesh 1 zero_lt_one,
    actual_inverse_lower C hG hC hMesh,
    forced_exponent A hG hMesh δ (((a+c+t : ℕ) : ℝ)+1) hδ (by positivity) d] with m hc hg he N period hN
  have hpos := IterationFour.Currency.g_pos hC N period (m+1) (by omega)
  have hc' : admittedCost A m ≤ (Pert.Asymptotics.regulatorRun C N period (m+1))⁻¹ := by
    simpa only [Real.rpow_neg_one] using hc N period hN
  have he' : ((a+c+t : ℕ) : ℝ)*Real.log (A.clock.hatBeta m) ≤
      pathRate A m*(A.clock.monitor m)^δ/(1+(A.clock.coverSize m : ℝ))^d := by
    have hz := Real.log_pos (A.fits.delayed m)
    nlinarith
  simpa only [neg_div, neg_mul] using flat_product (WardBin.hot A m) hpos
    (zero_le_one.trans (admittedCost_one A m)) hc' (hg N period hN) a c t he'

end YM.Integration.ActualRunAdmissionClock
end
