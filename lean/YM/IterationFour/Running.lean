import YM.IterationFour.Kinetic
import YM.Extension.UV.VacDemand
import YM.Next.WARD_BIN.Hats

/-!
# Currency conversion along the history

`b`-denominated = in inverse *square* coupling units. The hat clock (monotone)
is convenient for exponential weights; no assertion of any match of schemes.
Use `.g N q i` to spend in the declared expansion variable. Eventually always
means **first** select expansion/horizon/etc numbers, then work on a schedule
where those requirements hold, fixing only a *lower* reporting level; there
is no threshold on `N-i` nor deterioration along longer cutoff histories.

`stripe` is only for making magnitude/Lipschitz estimates on *finite* powers,
not asserting that one can apply the Markov machinery on this wider band.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Currency
open Function Filter Set Lattice Wilson RG IterationFour
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

abbrev B (a : Levels G) := a.clock.hatBeta
abbrev hat (a : Levels G) := a.clock.hatCoupling
abbrev g (C : Family G) := Pert.Asymptotics.regulatorRun C

def gain (b : ℝ) := (Real.sqrt b)⁻¹

/-- Fixed powers converted on any positive factor-4 band. -/
def stripe (b : ℝ) := Icc (b/4) (4*b)

lemma stripe_pos {b v : ℝ} (h : 0 < b) (he : v∈stripe b) : 0 < v := (div_pos h (by norm_num : (0:ℝ)<4)).trans_le he.1

lemma sizes_band {b v : ℝ} (hb : 0 < b) (h : v∈stripe b) :
    gain b ≤ 2*gain v ∧ gain v ≤ 2*gain b := by
  have hv := stripe_pos hb h
  have h4 : Real.sqrt 4 = 2 := by norm_num
  have ht : Real.sqrt v ≤ 2 * Real.sqrt b := by simpa [h4,Real.sqrt_mul (x:=4) (by norm_num : (0:ℝ)≤4)] using! Real.sqrt_le_sqrt h.2
  have hx : b ≤ 4*v := by linarith [h.1]
  have hs : Real.sqrt b ≤ 2*Real.sqrt v := by simpa [Real.sqrt_mul (x:=4) (by norm_num : (0:ℝ) ≤ 4),h4] using! Real.sqrt_le_sqrt hx
  unfold gain
  have h1:=Real.sqrt_pos.mpr hb; have h2:=Real.sqrt_pos.mpr hv
  constructor <;> field_simp <;> linarith

def gainFee (s : ℝ) := max ((1/4:ℝ)^(-s/2)) ((4:ℝ)^(-s/2))
def tiltFee (s : ℝ) := |(-s/2)| * gainFee (s+2)
lemma gainFee_pos (s : ℝ) : 0 < gainFee s := lt_of_lt_of_le (by positivity) (le_max_right ..)
lemma tiltFee_nonneg (s : ℝ) : 0 ≤ tiltFee s := mul_nonneg (abs_nonneg _) (gainFee_pos _).le

lemma rpGain (s : ℝ) {b : ℝ} (h : 0 < b) : gain b ^ s = b ^ (-s/2) := by
  have hv : gain b = b ^ (-(1/2:ℝ)) := by rw [Real.rpow_neg h.le,←Real.sqrt_eq_rpow]; rfl
  rw [hv,← Real.rpow_mul h.le]; ring_nf
lemma gain_receipt (s : ℝ) {b v : ℝ} (hb : 0 < b) (h : v∈stripe b) :
    gain v ^ s ≤ gainFee s * gain b ^ s := by
  have hv := stripe_pos hb h
  rw [rpGain s hv, rpGain s hb]
  set u := -s/2
  have hs:= Real.rpow_pos_of_pos hb u
  rcases le_total u 0 with hp|hp
  · have hh: (1/4:ℝ)*b ≤ v := by linarith [h.1]
    have hx := Real.rpow_le_rpow_of_nonpos (mul_pos (by norm_num) hb) hh hp
    rw [Real.mul_rpow (by norm_num) hb.le] at hx
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left ..) hs.le)
  have hx := Real.rpow_le_rpow hv.le h.2 hp
  rw [Real.mul_rpow (by norm_num) hb.le] at hx
  exact hx.trans (mul_le_mul_of_nonneg_right (le_max_right ..) hs.le)

lemma gain_compare (s : ℝ) {x y b : ℝ} (hp : 0 < b) (hx : x∈stripe b) (hy : y∈stripe b) :
    |gain x ^ s - gain y ^ s| ≤ tiltFee s * b⁻¹ * gain b ^ s * |x-y| := by
  rw [rpGain s (stripe_pos hp hx),rpGain s (stripe_pos hp hy)]
  let f' v := (-s/2)*v^(-s/2-1)
  refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f:=fun x:ℝ=> x^(-s/2)) (f':=f') (fun v h=> (Real.hasDerivAt_rpow_const (Or.inl (stripe_pos hp h).ne')).hasDerivWithinAt) ?_
    (convex_Icc _ _) hy hx
  intro v h
  have hv:=stripe_pos hp h
  have hφ := gain_receipt (s+2) hp h
  rw [rpGain _ hv,rpGain _ hp,show -(s+2)/2= -s/2-1 by ring] at hφ
  rw [Real.norm_eq_abs, show f' v= _ from rfl, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hv _)]
  refine (mul_le_mul_of_nonneg_left hφ (abs_nonneg _)).trans_eq ?_
  unfold tiltFee; rw [show -s/2-1= -1+(-s/2) by ring,Real.rpow_add hp,Real.rpow_neg_one, rpGain _ hp]; ring


lemma actual_band {C : Family G} (h : C.Makes) (N q i : ℕ) (hi : i≤N) :
    C.path.β N q i∈stripe (B C.path.levels i) := by
  let b := B C.path.levels i
  have hx : 0<b := zero_lt_one.trans (C.path.levels.fits.delayed _)
  have hh : C.path.β N q i ∈ Icc (b/2) (2*b) := (h.wilson.represents N q i hi).band
  exact ⟨(show b/4 ≤ b/2 by linarith).trans hh.1, hh.2.trans (show 2*b≤4*b by linarith)⟩
lemma hat_g {C : Family G} (h : C.Makes) (N q i : ℕ) (hi : i≤N) :
    hat C.path.levels i ≤ 2*g C N q i ∧ g C N q i ≤ 2*hat C.path.levels i :=
  sizes_band (WardBin.hot C.path.levels i) (actual_band h N q i hi)
lemma g_pos {C : Family G} (h : C.Makes) (N q i : ℕ) (hi : i≤N) : 0 < g C N q i :=
  inv_pos.mpr (Real.sqrt_pos.2 (stripe_pos (WardBin.hot C.path.levels i) (actual_band h N q i hi)))
lemma g_small {C : Family G} (hG : G.Simple) (h : C.Makes) (v : ℝ) (hv : 0<v) :
    ∀ᶠ i:ℕ in atTop, ∀ N q, i ≤ N → g C N q i < v := by
  have ht := Multi.Wage.small_hat hG C.path.levels
  filter_upwards [ht.eventually (gt_mem_nhds (half_pos hv))] with i hh N q hi
  exact ((hat_g h N q i hi).2).trans_lt (by linarith)

variable (a : Levels G)
def weight (s : ℝ) (m : ℕ) := (hat a m)^s
lemma weight_two (m : ℕ) : weight a 2 m = (B a m)⁻¹ := by
  unfold weight; rw [show hat a m=gain (B a m) from rfl, rpGain _ (WardBin.hot a m)]
  norm_num
  exact Real.rpow_neg_one (B a m)
lemma weight_pos (i : ℕ) (s : ℝ) : 0 < weight a s i := Real.rpow_pos_of_pos (WardBin.stepG ..) _
lemma weight_add (i : ℕ) (s t : ℝ) : weight a (s+t) i = weight a s i*weight a t i := Real.rpow_add (WardBin.stepG ..) s t
lemma beta_payment (i : ℕ) (s : ℝ) :
    B a i * weight a s i = weight a (s-2) i := by
  have h : weight a s i = weight a 2 i * weight a (s-2) i := by rw [← weight_add]; ring_nf
  rw [h,weight_two,mul_inv_cancel_left₀ (WardBin.hot a i).ne']
lemma across (hG : G.Simple) {s : ℝ} (h : 0≤ s) : Antitone (weight a s) := fun i j he =>
  Real.rpow_le_rpow ((WardBin.stepG a j).le) (inv_anti₀
    (Real.sqrt_pos.2 (WardBin.hot _ i)) (Real.sqrt_le_sqrt ((YM.Push.Corrected.Last.band_le a hG) he))) h
lemma weight_le (m : ℕ) {s t : ℝ} (h : s≤t) : weight a t m ≤ weight a s m :=
  Real.rpow_le_rpow_of_exponent_ge (WardBin.stepG a m) ((WardBin.stepGle a m).trans (a.fits.smallField m)) h
lemma buy (hG : G.Simple) (K : ℝ) {k : ℝ} (hk : 0 < k) {s t : ℝ} (hs : s<t) :
    ∀ᶠ m:ℕ in atTop, K * weight a t m ≤ k * weight a s m := by
  have hv := (Multi.Wage.small_hat hG a).rpow_const (Or.inr (sub_nonneg.mpr hs.le))
  rw [Real.zero_rpow (sub_pos.mpr hs).ne'] at hv
  have hf := hv.const_mul K
  rw [mul_zero] at hf
  filter_upwards [hf.eventually_le_const hk] with i he
  have ht : weight a t i = weight a (t-s) i * weight a s i := by rw [← weight_add,sub_add_cancel]
  rw [ht,← mul_assoc]; exact mul_le_mul_of_nonneg_right he ((weight_pos a i s).le)

omit a in
lemma g_weight {C : Family G} (h : C.Makes) {N q i : ℕ} (hi : i≤N) (s : ℝ) (hs : 0 ≤ s) :
    weight C.path.levels s i ≤ (2:ℝ)^s*(g C N q i)^s ∧ (g C N q i)^s ≤ (2:ℝ)^s*weight C.path.levels s i := by
  obtain ⟨hl,hv⟩ := hat_g h N q i hi
  have hg := g_pos h N q i hi
  have hx := WardBin.stepG C.path.levels i
  rw [weight, ← Real.mul_rpow (by norm_num) hg.le,← Real.mul_rpow (by norm_num) hx.le]
  exact ⟨Real.rpow_le_rpow hx.le hl hs,Real.rpow_le_rpow hg.le hv hs⟩

lemma force_payment (hG : G.Simple) (s : ℝ) :
    ∀ᶠ m : ℕ in atTop, Real.sqrt (a.clock.forcedAllowance m) ≤ weight a s m := by
  obtain ⟨d,hd⟩ := exists_nat_ge s
  filter_upwards [ (WardBin.pale a hG d).eventually_le_const zero_lt_one] with i hi
  refine le_trans ?_ (weight_le a i hd)
  unfold weight
  rw [Real.rpow_natCast]
  rw [inv_pow,inv_mul_le_iff₀ (pow_pos (WardBin.stepG _ _) _),mul_one] at hi
  exact hi
lemma threshold_receipt (m : ℕ) : ((a.budget m).threshold^2)⁻¹ ≤ B a m := by
  simpa only [inv_inv] using! inv_anti₀ (inv_pos.mpr (WardBin.hot ..)) (Extension.UV.threshold_large a m)

omit a in
lemma beta_gap_power {C : Family G} (s : ℝ) (m q : ℕ) (h : s ≤ 2*(q:ℝ)) :
    (IterationFour.Kinetic.price C m ^ q)⁻¹ ≤ weight C.path.levels s m := by
  let a := C.path.levels
  have ht := WardBin.hot a m
  have hy : B a m ≤ IterationFour.Kinetic.price C m := (show B a m ≤ 2 * B a m by linarith only [ht]).trans (IterationFour.Kinetic.two_hat_le C m)
  refine (inv_anti₀ (pow_pos ht _) (pow_le_pow_left₀ ht.le hy q)).trans (le_trans ?_ (weight_le a m h))
  change _ ≤ (hat a m)^(2*(q:ℝ))
  rw [Real.rpow_mul (WardBin.stepG a m|>.le),Real.rpow_natCast]
  change _ ≤ weight a 2 m ^ q
  rw [weight_two,inv_pow]
end YM.IterationFour.Currency
