import YM.Pert.Flow.ActionStep

/-!
# Physical path of beta -- uniform index/period/step prices

`m+1 → m`, factor L(m)=block m (of stage `J(m+1)`), calendar hats
used for thresholds/funding gates only. Use `gAt C N p` at both ends,
on *that* cutoff's path. No substitution of tolerance for an RG beta
error comparison. `logSize` is qpta's Λ, *not* the number of sites.

Window estimates all on the same Family and coupling; arbitrary fixed
powers k, don't extrapolate to order varying without a price proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG04B
open Function Filter Lattice Wilson RG Real
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge}
def logLedger (x : ℝ) := 2 + Real.log x
def logSize (a : Levels G) (m : ℕ) := logLedger (a.clock.hatBeta m)
def ySize (x : ℝ) := 1 + Real.log (logLedger x)
def geo (a : Levels G) (m : ℕ) := ySize (a.clock.hatBeta m)
def ratio (a : Levels G) (m : ℕ) : ℝ := (a.S.block m).val
def stride (a : Levels G) (m : ℕ) := Real.log (ratio a m)
/-- Coupling variable *as used* in this task; no hatted prices in it. -/
abbrev gAt (C : Family G) (N p m : ℕ) := Pert.Asymptotics.regulatorRun C N p m

section Level
variable (a : Levels G) (hG : G.Simple)
local notation "ℓ" => logSize a
local notation "s" => a.S.scale
local notation "B" => a.clock.hatBeta

lemma logSize_hi (m : ℕ) : 2 ≤ ℓ m := le_add_of_nonneg_right (Real.log_nonneg (a.fits.delayed m).le)
lemma geo_eq (m : ℕ) : geo a m = 1 + Real.log (ℓ m) := rfl
lemma geo_hi (m : ℕ) : 1 ≤ geo a m := le_add_of_nonneg_right (Real.log_nonneg (one_le_two.trans (logSize_hi a m)))
lemma ratio_lo (m : ℕ) : 3 ≤ ratio a m := by
  unfold ratio; exact_mod_cast a.S.block_large m
lemma stride_lo (m : ℕ) : Real.log 3 ≤ stride a m := Real.log_le_log (by norm_num) (ratio_lo ..)
lemma stride_pos (m : ℕ) : 0 < stride a m := (Real.log_pos (by norm_num : (1:ℝ)<3)).trans_le (stride_lo ..)
lemma distance_step (m : ℕ) : s (m+1)= s m + stride a m := Schedule.scale_succ ..
lemma hat_step (m : ℕ) : B (m+1) = B m + G.slopeConstant * stride a m := by
  simp only [Calendar.hatBeta, distance_step a, mul_add, add_assoc]

include hG
lemma risingHat : Tendsto B atTop atTop := tendsto_atTop_add_const_left _ _
  (a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
lemma strictHat : StrictMono B := strictMono_nat_of_lt_succ fun m => by
  rw [hat_step a]; exact lt_add_of_pos_right _ (mul_pos (Gauge.slopeConstant_pos hG) (stride_pos ..))

omit a hG in
lemma endlessLedger : Tendsto logLedger atTop atTop :=
  tendsto_atTop_add_const_left _ 2 Real.tendsto_log_atTop
omit a hG in
lemma geoEnd : Tendsto ySize atTop atTop :=
  tendsto_atTop_add_const_left _ 1 (Real.tendsto_log_atTop.comp endlessLedger)

lemma persist : Tendsto ℓ atTop atTop := endlessLedger.comp (risingHat a hG)
lemma starboard : Tendsto (geo a) atTop atTop := geoEnd.comp (risingHat a hG)
lemma monotone_logSize : Monotone ℓ := fun _ _ hij => add_le_add_right
  (Real.log_le_log (lt_trans zero_lt_one (a.fits.delayed _)) ((strictHat a hG).monotone hij)) _
lemma monotone_geo : Monotone (geo a) := fun _ _ hij => add_le_add_right
  (Real.log_le_log (zero_lt_two.trans_le (logSize_hi ..)) (monotone_logSize a hG hij)) _

/-- Λ^k/s spacing budget. -/
theorem indexPrice (k : ℕ) : Tendsto (fun i : ℕ => ℓ i ^ k / s i) atTop (𝓝 0) := by
  have hn : B =O[atTop] s := by
    -- bigO on sequences
    unfold Calendar.hatBeta
    exact ((Asymptotics.isLittleO_const_left.mpr (Or.inr (by simpa using!
      (tendsto_abs_atTop_atTop.comp a.S.divergent)))).isBigO).add
        ((Asymptotics.isBigO_refl s atTop).const_mul_left _)
  have hlog : Tendsto (fun i=>Real.log (B i)) atTop atTop := Real.tendsto_log_atTop.comp (risingHat a hG)
  have he : ℓ =O[atTop] (fun i=>Real.log (B i)) :=
      ((Asymptotics.isLittleO_const_left.mpr (Or.inr (by simpa using!
        (tendsto_abs_atTop_atTop.comp hlog)))).isBigO).add (Asymptotics.isBigO_refl _ _)
  exact (Asymptotics.IsLittleO.trans_isBigO ((he.pow k).trans_isLittleO
    (Real.isLittleO_pow_log_id_atTop (n:=k)|>.comp_tendsto (risingHat a hG))) hn).tendsto_div_nhds_zero

/-- Uniformity on any of the *same schedule's* polynomial-log windows.
`lo` a required starting tail index (from other producers). -/
theorem indices (lo k : ℕ) (r : ℝ) : ∀ᶠ m in atTop, ∀ i ≤ m,
    s m - s i ≤ r*ℓ m^k → lo ≤ i ∧ ℓ i ≤ ℓ m ∧ B m ≤ 2*B i := by
  have h := Tendsto.const_mul r (indexPrice a hG k); rw [mul_zero] at h
  filter_upwards [h.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2)),
      a.S.divergent.eventually_ge_atTop (2*s lo), a.S.divergent.eventually_gt_atTop 0] with m hp hv hs i hi he
  have h₀ : r*ℓ m^k/s m ≤ 1/2 := by rw [mul_div_assoc]; exact hp
  have h₁ := (div_le_iff₀ hs).mp h₀
  have hx : s m ≤ 2*s i := by linarith
  have hm : StrictMono s := strictMono_nat_of_lt_succ fun i => by
    rw [distance_step a]; exact lt_add_of_pos_right _ (stride_pos ..)
  refine ⟨hm.le_iff_le.mp (by linarith), monotone_logSize a hG hi, ?_⟩
  unfold Calendar.hatBeta
  have hK := mul_le_mul_of_nonneg_left hx (Gauge.slopeConstant_pos hG).le
  change a.clock.bar + G.slopeConstant*s m ≤ 2*(a.clock.bar + G.slopeConstant*s i)
  linarith only [a.clock.bar_pos,hK]

omit hG
lemma stepsPay {m i : ℕ} (h : i ≤ m) : (m-i:ℕ) * Real.log 3 ≤ s m - s i := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [distance_step a, show m+1-i=m-i+1 by omega,Nat.cast_add_one,add_mul,one_mul]
    linarith only [ih,stride_lo a m]
end Level

section Uniform
variable {C : Family G} (hC : C.Makes) (hG : G.Simple)
include hC
set_option quotPrecheck false
local notation "a" => C.path.levels
local notation "L" => ratio a
local notation "ℓ" => logSize a
local notation "B" => C.path.levels.clock.hatBeta
local notation "s" => C.path.levels.S.scale
local notation "β" => C.path.β

lemma inBand (N p m : ℕ) (h : m ≤ N) : B m/2 ≤ β N p m ∧ β N p m ≤ 2*B m :=
  (hC.wilson.represents _ _ _ h).band
@[simp] lemma beta_positive (N p m : ℕ) (h : m ≤ N) : 0 < β N p m :=
  (half_pos <| zero_lt_one.trans (C.path.levels.fits.delayed m)).trans_le (inBand hC N p m h).1
lemma running_pos (N p m : ℕ) (h : m ≤ N) : 0 < gAt C N p m :=
  inv_pos.mpr (Real.sqrt_pos.mpr (beta_positive hC N p m h))
lemma reset_sq (N p m : ℕ) (h : m ≤ N) : (gAt C N p m)⁻¹ ^ 2 = β N p m := by
  change ((Real.sqrt (β N p m))⁻¹)⁻¹ ^ 2 = _
  rw [inv_inv, Real.sq_sqrt (beta_positive hC _ _ _ h).le]
lemma read_beta (N p m : ℕ) (h : m ≤ N) : Real.log (gAt C N p m) = - Real.log (β N p m) / 2 := by
  change Real.log (Real.sqrt _)⁻¹ = _
  rw [Real.log_inv, Real.log_sqrt (beta_positive hC N p m h).le]; ring

include hG
/-- Coupling power is comparable to exponential in Λ (not scale!), uniformly. -/
theorem runningLogs : ∀ᶠ m : ℕ in atTop, ∀ N p, m ≤ N →
    -(ℓ m) ≤ Real.log (gAt C N p m) ∧ Real.log (gAt C N p m) ≤ -ℓ m/4 := by
  have h₀ := Real.tendsto_log_atTop.comp (risingHat a hG)
  have hz : 0 < Real.log 2 := Real.log_pos one_lt_two
  filter_upwards [h₀.eventually_ge_atTop (4*Real.log 2+10)] with m hm N p hr
  obtain ⟨hf,hb⟩:= inBand hC N p m hr
  have hT : 0 < B m := zero_lt_one.trans (C.path.levels.fits.delayed m)
  have h₁ := Real.log_le_log (beta_positive hC _ _ _ hr) hb
  have h₂ := Real.log_le_log (half_pos hT) hf
  rw [Real.log_mul (by norm_num) hT.ne'] at h₁
  rw [Real.log_div hT.ne' (by norm_num)] at h₂
  change _ ≤ Real.log (B m) at hm
  rw [read_beta hC _ _ _ hr]; change -(2+Real.log (B m)) ≤ _ ∧ _ ≤ -(2+Real.log (B m))/4
  constructor <;> linarith

lemma coupling_exit {c : ℝ} (hc : 0 < c) : ∀ᶠ m : ℕ in atTop, ∀ N p, m ≤ N →
    gAt C N p m ≤ c := by
  filter_upwards [runningLogs hC hG,(persist a hG).eventually_ge_atTop (-4*Real.log c)] with m h hℓ N p hm
  apply (Real.log_le_log_iff (running_pos hC _ _ _ hm) hc).1
  exact ((h N p hm).2).trans (by linarith)

private lemma gainStep : ∀ᶠ m : ℕ in atTop, ∀ N p, m < N →
    (G.slopeConstant/2) * stride a m ≤ β N p (m+1) - β N p m ∧
      β N p (m+1) - β N p m ≤ 2 * G.slopeConstant * stride a m := by
  have hk := Gauge.slopeConstant_pos hG
  filter_upwards [Pert.Flow.drift_price (C:=C) |>.eventually (ge_mem_nhds (half_pos hk))] with m h N p hm
  obtain ⟨hl,hh⟩:=abs_le.mp (hC.wilson.steps N p m hm).2
  have h0 := stride_pos a m
  have hj : (C.path.levels.params (m+1)).drift ≤ G.slopeConstant/2 * stride a m := (div_le_iff₀ h0).1 h
  change _ ≤ β N p (m+1) - β N p m - G.slopeConstant * stride a m at hl
  change β N p (m+1) - β N p m - G.slopeConstant * stride a m ≤ _ at hh
  constructor <;> linarith only [hj,hl,hh,mul_pos hk h0]

/-- C.Makes has enough drift for monotone actual g on every such trajectory tail. -/
theorem downhill : ∀ᶠ m : ℕ in atTop, ∀ N p, m < N → gAt C N p (m+1) ≤ gAt C N p m := by
  filter_upwards [gainStep hC hG] with m h N p hm
  have he := ((mul_pos (half_pos (Gauge.slopeConstant_pos hG)) (stride_pos ..)).trans_le (h N p hm).1).le
  apply inv_anti₀ (Real.sqrt_pos.2 (beta_positive hC _ _ _ hm.le))
  exact Real.sqrt_le_sqrt (sub_nonneg.mp he)

/-- Same path actual increment bill (also pays perturbative reset consumers'
elastic windows). The sunk slack is NOT a fresh error term at each step. -/
theorem budgetBeta : ∀ᶠ lo in atTop, ∀ N p i j : ℕ, lo ≤ i → i ≤ j → j ≤ N →
    (G.slopeConstant/2) * (s j-s i) ≤ β N p j - β N p i ∧
      β N p j - β N p i ≤ 2*G.slopeConstant*(s j - s i) := by
  obtain ⟨k,hk⟩:= eventually_atTop.1 (gainStep hC hG)
  filter_upwards [eventually_ge_atTop k] with lo hlo N p i j hm hi hj
  induction j, hi using Nat.le_induction with
  | base => simp
  | succ j hJ ih =>
    rw [distance_step a]
    obtain ⟨H,K⟩:= ih ((Nat.le_add_right ..).trans hj); obtain ⟨U,W⟩:= hk _ (hlo.trans (hm.trans hJ)) N p hj
    constructor <;> linarith

/-- The actual g at every interior step of polylog windows is comparable
uniformly; fine and coarse endpoints on *this* cutoff share the band. -/
theorem windowCoupling (lo k : ℕ) (t : ℝ) : ∀ᶠ m in atTop, ∀ N p : ℕ, m ≤ N → ∀ i ≤ m,
    s m - s i ≤ t*ℓ m ^ k →
      lo ≤ i ∧ gAt C N p m ≤ gAt C N p i ∧ gAt C N p i ≤ 4*gAt C N p m := by
  obtain ⟨u,hu⟩:= eventually_atTop.1 (budgetBeta hC hG)
  filter_upwards [indices a hG (max u lo) k t] with m hh N p hN i hi he
  obtain ⟨hY,-,hZ⟩:= hh i hi he
  have hb:= hu u le_rfl N p i m ((le_max_left ..).trans hY) hi hN
  have hs : s i ≤ s m := (monotone_nat_of_le_succ fun i =>
    (by rw [distance_step a]; exact le_add_of_nonneg_right (stride_pos _ _).le : s i ≤ s (i+1))) hi
  let v := Real.sqrt (β N p m); let w := Real.sqrt (β N p i)
  have hK := beta_positive hC N p i (hi.trans hN)
  have hv : 0 < v := Real.sqrt_pos.2 (beta_positive hC N p m hN)
  have hw : 0 < w := Real.sqrt_pos.2 hK
  have ha := sub_nonneg.mp <| (mul_nonneg (half_pos (Gauge.slopeConstant_pos hG)).le (sub_nonneg.mpr hs)).trans hb.1
  have hg : v ≤ 4*w := by
    have hx:= Real.sq_sqrt hK.le
    have hy:= Real.sq_sqrt (beta_positive hC N p m hN).le
    have hh : β N p m ≤ 16* β N p i := by linarith only [hK,hZ,(inBand hC N p i (hi.trans hN)).1,(inBand hC N p m hN).2]
    change v^2=_ at hy; change w^2=_ at hx; nlinarith
  refine ⟨(le_max_right ..).trans hY,inv_anti₀ hw (Real.sqrt_le_sqrt ha),?_⟩
  change w⁻¹ ≤ 4*v⁻¹
  rw [← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ hw hv).2 (by simpa using hg)
end Uniform
end YM.RG04B
