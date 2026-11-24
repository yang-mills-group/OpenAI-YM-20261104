import YM.MS.Dial.Signals
import YM.XSpace.Layout

/-!
# A regulator where the literal removal results apply

Even inversion / constant blocks / long period. Every step uses the *same*
run. Top lattice spacings `ratio^-n`. MS `θ = log(1/a)`. Give a sample at
actual scaled positions (including submesh discrepancy). Shift the start finitely
so all probes clear. No uniformity assumed from pointwise conditions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Schedule
open Function Filter Set Finset XSpace XSpace.Period
open MS MS.Tone MS.Vista MS.Fleet MS.Plane MS.Latch MS.Rake MS.Orbit MS.Dial MS.Tide
open Lattice
open scoped Topology ContDiff BigOperators

def half (R : Period) : Side :=
  ⟨R.side.val / 2, by
    have ht := R.large
    omega⟩

lemma twice (R : Period) : periodN (half R) = R.side := by
  apply Subtype.ext
  change 2 * (half R).val = R.side.val
  have h := R.even
  unfold half
  dsimp
  omega

abbrev island {I : Type} (f : I → Side) (i : I) (h : 4 ≤ (dimT f i).val) : Period :=
  ⟨dimT f i, ⟨(f i).val, rfl⟩, h⟩
variable (Z : Run)

def lengths (n : ℕ) :=
  (Z.step n).p

abbrev strand (n : ℕ) :=
  half (lengths Z n)

lemma length_strand (n : ℕ) : dimT (strand Z) n = (lengths Z n).side :=
  twice _

lemma strand_ok (n : ℕ) : 4 ≤ (dimT (strand Z) n).val := by
  rw [length_strand]
  exact (lengths Z n).large

def stage (n : ℕ) :=
  (n : ℝ) * Real.log (Z.ratio : ℝ)

def contextS (μ : ℝ) : Geo ℕ :=
  ⟨stage Z, fun i => μ - stage Z i, fun i =>
    mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg
        (by
          have h := Z.large
          exact_mod_cast (show 1 ≤ Z.ratio by omega)))⟩

lemma stage_up : Tendsto (stage Z) atTop atTop := by
  have he : 0 < Real.log (Z.ratio : ℝ) :=
    Real.log_pos
      (by
        have h := Z.large
        exact_mod_cast (show 1 < Z.ratio from (by omega)))
  exact tendsto_natCast_atTop_atTop.atTop_mul_const he

lemma mesh (n : ℕ) : (Z.step n).spacing = Real.exp (-stage Z n) := by
  rw [Real.exp_neg, stage, Real.exp_nat_mul,
    Real.exp_log
      (by
        exact_mod_cast
          (show 0 < Z.ratio by
            have h := Z.large
            omega))]
  change (↑(Z.ratio ^ n) : ℝ)⁻¹ = _
  push_cast
  rfl

lemma generous : Super atTop (strand Z) (stage Z) := by
  intro c
  let v := Real.log (Z.ratio : ℝ)
  have he : 0 ≤ v :=
    Real.log_nonneg
      (by
        have h := Z.large
        exact_mod_cast (show 1 ≤ Z.ratio by omega))
  let Y := Z.finalSide
  let F := Y.side.val
  have hy : 0 < (F : ℝ) := by exact_mod_cast Y.side.pos
  have hv : 0 ≤ Real.log (F : ℝ) := Real.log_nonneg (by exact_mod_cast Y.side.pos)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop c)] with n hn
  rw [tickA, length_strand]
  change _ ≤ Real.log (↑(F * Z.ratio ^ (n + Z.reserve * n * n)) : ℝ)
  push_cast
  rw [Real.log_mul hy.ne'
      (pow_ne_zero _
        (by
          have h := Z.large
          exact_mod_cast (show Z.ratio ≠ 0 by omega))),
    Real.log_pow]
  change c * (n * v) ≤ Real.log (F : ℝ) + _ * v
  apply le_trans _ (le_add_of_nonneg_left hv)
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ he
  have ht : 1 ≤ (Z.reserve : ℝ) := by exact_mod_cast Z.spare
  push_cast
  calc
    _ ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_right (show c ≤ (n : ℝ) from hn) (by positivity)
    _ ≤ ↑Z.reserve * n * n := by
      gcongr
      exact le_mul_of_one_le_left (by positivity) ht
    _ ≤ _ := le_add_of_nonneg_left (by positivity)

def midpoint (R : Side) : Cover := fun _ => (↑(R.val / 4) : ℤ)

lemma center_is (R : Side) (h : 4 ≤ R.val) : Lattice.lift (wrap R (midpoint R)) = midpoint R := by
  apply lift_eq_iff.mpr
  exact
    ⟨rfl, fun _ => by
      unfold midpoint
      omega⟩

lemma center_price (L : Side) (h : 4 ≤ (periodN L).val) (k : Half) :
    Vista.mine (periodN L) (wrap (periodN L) (midpoint (periodN L)) - thin L k) := by
  let n := periodN L
  let C := wrap n (midpoint n)
  let u := thin L k
  have H : pdist C = n.val / 4 := by
    unfold pdist C
    rw [center_is n h]
    apply le_antisymm
    · apply Finset.sup_le
      intro _ _
      unfold midpoint
      omega
    exact
      (show n.val / 4 = (midpoint n 0).natAbs by
            unfold midpoint
            omega).le.trans
        (Finset.le_sup (b := 0) (f := fun i => (midpoint n i).natAbs) (Finset.mem_univ _))
  by_cases he : k = 0
  · unfold mine
    rw [he, map_zero, sub_zero]
    change n.val ≤ 16 * pdist C
    rw [H]
    change 4 ≤ n.val at h
    omega
  have ht : pdist u ≤ pdist (C - u) + pdist C := by
    nth_rw 1 [show u = C + -(C - u) by abel]
    exact (pdist_triangle _ _).trans (le_of_eq (by rw [pdist_neg, Nat.add_comm]))
  rw [show pdist u = L.val from
      (Vista.caress ..).trans
        (by
          rw [bornlf k he]
          simp)] at ht
  change n.val ≤ 16 * pdist (C - u)
  rw [H] at ht
  have hv : n.val = 2 * L.val := cap_val L
  omega

def roundP (u : ℝ) (x : QP) : Cover := fun i => ⌊Real.exp u * x i⌋

lemma roundP_near (u : ℝ) (x : QP) : ‖Tone.embed (roundP u x) - Real.exp u • x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  apply abs_le.2
  let z := Real.exp u * x i
  have he := Int.floor_le z
  have ht := Int.lt_floor_add_one z
  change -(1 : ℝ) ≤ ((⌊z⌋ : ℤ) : ℝ) - z ∧ ((⌊z⌋ : ℤ) : ℝ) - z ≤ 1
  constructor <;> linarith

lemma roundP_bank (u : ℝ) (x : QP) (hp : 0 ≤ u) :
    ‖Tone.embed (roundP u x)‖ ≤ (1 + ‖x‖) * Real.exp u := by
  let S := roundP u x
  let i := Real.exp u
  let q := i • x
  have ht := norm_add_le (Tone.embed S - q) q
  rw [sub_add_cancel] at ht
  apply ht.trans
  change _ + ‖i • x‖ ≤ _
  rw [norm_smul_of_nonneg (Real.exp_pos _ |>.le)]
  apply le_trans (add_le_add_left (roundP_near u x) _)
  linarith [Real.one_le_exp hp]

lemma roundP_test (u : ℝ) (x : QP) : ‖Real.exp (-u) • Tone.embed (roundP u x) - x‖ ≤ Real.exp (-u) := by
  rw [show
      Real.exp (-u) • Tone.embed (roundP u x) - x =
        Real.exp (-u) • (Tone.embed (roundP u x) - Real.exp u • x)
      by rw [smul_sub, Real.exp_neg u, inv_smul_smul₀ (Real.exp_ne_zero u)],
    norm_smul_of_nonneg (Real.exp_pos _ |>.le)]
  exact mul_le_of_le_one_right (Real.exp_pos _ |>.le) (roundP_near ..)

variable {W : Type}

def shot (d : ℕ) (X : W → QP) (μ : ℝ) : Trial ℕ W
    where
  profile :=
    ⟨fun i => stage Z (i + d), fun i => μ - stage Z (i + d), fun i => (contextS Z μ).room (i + d)⟩
  side i := strand Z (i + d)
  off w i := roundP (stage Z (i + d)) (X w)
  head i := midpoint (dimT (strand Z) (i + d))

lemma advance (d : ℕ) : Tendsto (fun i : ℕ => i + d) atTop atTop :=
  StrictMono.tendsto_atTop fun _ _ h => Nat.add_lt_add_right h d

lemma photographed (d : ℕ) (X : W → QP) (μ : ℝ) : Tendsto (testP (shot Z d X μ)) atTop (𝓝 X) := by
  apply tendsto_pi_nhds.mpr
  intro w
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp_rw [dist_eq_norm]
  refine
    squeeze_zero (fun _ => norm_nonneg _) (fun i => roundP_test (stage Z (i + d)) (X w))
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ((stage_up Z).comp (advance d))))

lemma shot_large (d : ℕ) (X : W → QP) (μ : ℝ) (i : ℕ) : 4 ≤ (dimT (shot Z d X μ).side i).val :=
  strand_ok Z _
variable [LinearOrder W] [Fintype W]

lemma usable (X : W → QP) (h : Injective X) (μ : ℝ) : ∃ d : ℕ, Dial.Uses (shot Z d X μ) atTop μ := by
  obtain ⟨n, hn⟩ := eventually_atTop.mp ((photographed Z 0 X μ).eventually (earlyW h))
  let F := shot Z n X μ
  have hh i : Clamp X (testP F i) := hn (i + n) (by omega)
  refine
    ⟨n,
      ⟨fun w => ⟨1 + ‖X w‖, by positivity, fun i => roundP_bank _ _ (F.profile.room i)⟩, ?_, fun _ =>
        rfl, (stage_up Z).comp (advance n), fun c => (advance n).eventually (generous Z c), fun i k =>
        center_price _ (strand_ok Z (i + n)) k,
        centered_size _ _ fun i => (center_is _ (strand_ok Z (i + n))).symm⟩⟩
  apply unpose (v := μ) F.off
  intro i j hp
  let v := ‖X i - X j‖
  have hv : 0 < v := norm_pos_iff.mpr (sub_ne_zero.mpr (h.ne hp))
  refine
    ⟨⟨2 * v, mul_pos (by norm_num) hv, fun k => ?_⟩, ⟨v / 2, div_pos hv (by norm_num), fun k => ?_⟩⟩
  all_goals
    simp only [Geo.roots, Pi.zero_apply, Real.exp_zero, mul_one]
    first
    | exact (hh k i j hp |>.2).le
    | exact (hh k i j hp |>.1).le
end YM.WilsonMS.Schedule
