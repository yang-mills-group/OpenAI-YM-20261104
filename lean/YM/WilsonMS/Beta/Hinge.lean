import YM.WilsonMS.Beta.PowerCurrent
import YM.WilsonMS.ScaleFlow.Permanent
/-!
# Transfer differences of marginal jets to real scale law

Marginal jets need not converge separately here. Matching tells us their
*differences* converge. y at that test is fixed. Cannot use a bound on
derivatives just at points bounded away from 0; need the momentum jet
estimates, here used on rays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric List
open LoopRank Lattice MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect
  Native Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal Cylinder Lab Menus Lifting Landau.Detect.Mark Wind
  High Knobs Rider
open LogTime LogTime.IntervalFamily Outlook Land
open Rock Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem
  Mell Logarithm Pearl Train Dock Emit
open PowerSeries (coeff)
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {b : Bool} {X Y : Reading G} {h : ℤ} {n r : ℕ}

lemma jet_match (x : ℝ) (w : Legs (Lane4 G)) (j : ℕ) (hm : fieldDim wfield w + j = h)
    (hp : Course b w) (hq : Trust b h X Y w.length)
    (hf : ∀ t : ℝ, ContDiff ℝ ∞ (fieldVal (X (x, t)) (ray w)))
    (hT : ∀ t : ℝ, ContDiff ℝ ∞ (fieldVal (Y (x, t)) (ray w))) :
    Tendsto (fun t : ℝ => torch j (X (x, t) - Y (x, t)) w) atTop (𝓝 0) := by
  let T := ray w
  have hx := (hq ℝ T (ray_course hp) (ray_len w))
  obtain ⟨C, hC, k, hk⟩ := hx.gain.quoted j
  suffices HV : Origin (X - Y) T j x 0
    by
    have hk t : ContDiff ℝ ∞ (Domain.tape (X - Y) T x t) := (hf t).sub (hT t)
    obtain h := origin_test HV hk 1
    rw [show sail T 1 = w from ray_sail w] at h
    simpa [Tensor.diagonal, Pi.sub_apply] using h
  unfold Origin
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  let k0 := 1 + |x|
  apply
    squeeze_zero' (g := fun i : ℝ => C * k0 ^ k * polyExp eps_gain k i)
      (Eventually.of_forall (fun i => norm_nonneg _))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with i hi
    let v := meet.choose x i hi
    obtain he := hk v 0 trivial
    apply he.trans_eq
    rw [show fieldDim wfield T = fieldDim wfield w from ray_dim _,
      show fieldDim wfield w - h = -(j : ℤ) from (by omega)]
    change
      C * (k0 * (1 + i) * (1 + exp i * ‖(0 : ℝ)‖)) ^ k *
          (exp i ^ (-(j : ℤ)) * exp (-eps_gain * i) * exp i ^ j) =
        _
    simp only [norm_zero, mul_zero, add_zero, mul_one, mul_pow, zpow_neg, zpow_natCast]
    rw [mul_right_comm (exp i ^ j)⁻¹, inv_mul_cancel₀ (pow_ne_zero _ (exp_pos i).ne'), one_mul]
    unfold polyExp
    ring
  exact (show C * k0 ^ k * 0 = 0 from mul_zero _) ▸ (vanishes p_gain k).const_mul _

variable {B : Local.Physical.Deck G} {M : Booked B} (F : MS_Data G M)
set_option quotPrecheck false

lemma archive_disc : Disc true 1 (Archive 4 F.bulk) (Archive 4 F.bulk) ((2 : ℂ)⁻¹) 4 :=
  dock F.bulkOK Motif.wisdom

lemma archive_plowed (n : ℕ) (t x : ℝ) (w : Legs (Lane4 G)) :
    Archive 4 F.bulk n (x, t) w =
      exp t ^ (fieldDim wfield w - 4) • Archive 4 F.bulk n (x + t, 0) (sail (ray w) (exp t)) := by
  have hx := Host.host (gang (F.bulkOK n))
  obtain ⟨p, hP⟩ := tallP (Moony.toast hx.bill)
  unfold Archive four
  dsimp only
  rw [vertical hP hx.tall, vertical hP hx.tall, add_zero, posing]
  unfold plow
  rw [show -(((4 : ℕ) : ℂ)) + _ = ((fieldDim wfield w - 4 : ℤ) : ℂ) from ?_, Port.τ_amt,
    Complex.real_smul, ray_go]
  rfl
  norm_cast
  change (-4 : ℤ) + fieldDim wfield w = fieldDim wfield w - 4
  abel

lemma breathing (n : ℕ) (x t : ℝ) (w : Legs (Lane4 G)) :
    ContDiff ℝ ∞ (fieldVal (Archive 4 F.bulk n (x, t)) (ray w)) :=
  Outlook.hair (Host.host (gang (F.bulkOK n))) (n := 0) (ray w)

private lemma stretch (z : ℝ) (f : ℝ → ℂ) (H : ContDiff ℝ ∞ f) (j : ℕ) :
    iteratedDeriv j (fun x : ℝ => f (z • x)) 0 = z ^ j • iteratedDeriv j f 0 := by
  unfold iteratedDeriv
  rw [iteratedFDeriv_comp_const_smul z (H.of_le (by exact_mod_cast le_top))]
  dsimp only
  rw [smul_zero]
  rfl

lemma margin (y t : ℝ) (w : Legs (Lane4 G)) (j : ℕ) (hm : fieldDim wfield w + j = 4) :
    torch j (Archive 4 F.bulk n (y, t)) w = torch j (Archive 4 F.bulk n (y + t, 0)) w := by
  let Z := exp t
  let f := fieldVal (Archive 4 F.bulk n (y + t, 0)) (ray w)
  have he (u : ℝ) : fieldVal (Archive 4 F.bulk n (y, t)) (ray w) u = (Z ^ (-(j : ℤ))) • f (Z • u) := by
    unfold f fieldVal
    rw [archive_plowed, sail_dim, ray_dim, show fieldDim wfield w - 4 = -(j : ℤ) from (by omega)]
    simp only [ray_go, List.map_map, Function.comp_def, Z, smul_smul, smul_eq_mul]
  simp_rw [torch_at]
  change reading j (fieldVal (Archive 4 F.bulk n (y, t)) (ray w)) = reading j f
  rw [funext he]
  unfold reading
  have hh : ContDiff ℝ ∞ f := breathing ..
  rw [show (fun x => Z ^ (-(j : ℤ)) • f (Z • x)) = Z ^ (-(j : ℤ)) • (fun x : ℝ => f (Z • x)) from rfl,
    iteratedDeriv_const_smul, stretch Z f hh j, zpow_neg, zpow_natCast,
    inv_smul_smul₀ (pow_ne_zero _ (exp_pos t |>.ne'))]
  exact
    ContDiffAt.of_le (hh.comp (f := fun z : ℝ => Z • z) (by fun_prop) |>.contDiffAt)
      (by exact_mod_cast le_top)
open GFlow

lemma ready_marg (t : ℝ) (n : ℕ) (w : Legs (Lane4 G)) (j : ℕ) :
    Ready fun x : ℝ => torch j (Archive 4 F.bulk n (x, t)) w := by
  obtain ⟨v, hv⟩ := (archive_disc F).master.poly n
  let f (x : ℝ) := fieldVal (Archive 4 F.bulk n (x, t)) (ray w)
  have ht x : f x = (∑ i ∈ Finset.range v, (plate v i).eval x • f i) := by
    unfold f
    rw [show
        (Archive 4 F.bulk) n (x, t) =
          (∑ i ∈ Finset.range v, (plate v i).eval x • (Archive 4 F.bulk n (i, t)))
        from ?_]
    · ext u
      rw [Finset.sum_apply, fieldVal, Finset.sum_apply]
      rfl
    exact Eq.trans (congr_fun (interpret hv x) t) (Finset.sum_apply t _ _)
  have hh (x : ℝ) :
    iteratedFDeriv ℝ j (f x) 0 =
      ∑ i ∈ Finset.range v, (plate v i).eval x • iteratedFDeriv ℝ j (f i) 0 := by
    let H := Finset.range v
    let U (i : ℕ) := (plate v i).eval x • f i
    let P (i : ℕ) := iteratedFDeriv ℝ j (f i) 0
    have hm (i : ℝ) : ContDiff ℝ ↑j (f i) := (breathing F n i t w).of_le (by exact_mod_cast le_top)
    nth_rw 1 [ht]
    have hx (K : Finset ℕ) : ContDiff ℝ ↑j (∑ i ∈ K, U i) := by
      induction K using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        exact contDiff_const
      | insert i K hk ih =>
        rw [Finset.sum_insert hk]
        exact ((show ContDiff ℝ ↑j (U i) from (hm i).const_smul ((plate v i).eval x))).add ih
    change iteratedFDeriv ℝ j (∑ i ∈ H, U i) 0 = ∑ i ∈ H, _ • P i
    induction H using Finset.induction_on with
    | empty => simp
    | insert i K hp ih =>
      rw [Finset.sum_insert hp, Finset.sum_insert hp,
        iteratedFDeriv_add (show ContDiff ℝ ↑j (U i) from (hm i).const_smul ((plate v i).eval x))
          (hx _),
        Pi.add_apply, ih,
        show iteratedFDeriv ℝ j (U i) 0 = _ from iteratedFDeriv_const_smul_apply (hm _ |>.contDiffAt)]
  have hm (x : ℝ) :
    torch j (Archive 4 F.bulk n (x, t)) w =
      ∑ i ∈ Finset.range v, (plate v i).eval x • torch j (Archive 4 F.bulk n ((i : ℕ), t)) w := by
    simp_rw [torch_at, reading, iteratedDeriv]
    change (↑j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j (f x) 0 (fun _ => 1) = _
    rw [hh x, _root_.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => smul_comm ..)
  convert
    accounts (Finset.range v) (f := fun i x =>
      (plate v i).eval x • torch j (Archive 4 F.bulk n ((i : ℕ), t)) w)
      (fun i _ => status (plate v i) _) using
    1
  exact funext hm

lemma read_delta {X : Dec G} {T : Team} (hX : PC G T X)
    (hp : Fixed (col X) (Archive 4 F.bulk) true 4 1) (n : ℕ) (hn : 0 < n) (x y t : ℝ)
    (w : Legs (Lane4 G)) (hs : Course true w) (hL : 0 < w.length) (j : ℕ)
    (hh : fieldDim wfield w + j = 4) (d : ℂ)
    (hx : ∀ t : ℝ, torch j (col X n (x, t) - col X n (y, t)) w = d) :
    torch j (Archive 4 F.bulk n (x, t) - Archive 4 F.bulk n (y, t)) w = d := by
  have hu (x t : ℝ) : ContDiff ℝ ∞ (fieldVal (col X n (x, t)) (ray w)) :=
    (hX.owes n |>.stay x).joint.routine _ _
  let P (u v : ℝ) := torch j (Archive 4 F.bulk n (u, v)) w
  have he (x : ℝ) :=
    jet_match (X := col X n) x w j hh hs (hp n hn w.length (fun _ => hL)) (hu x)
      (fun p => breathing F n x p w)
  have hM := (he y).sub (he x)
  rw [sub_self] at hM
  have hh' (u v : ℝ) : P u v = P (u + v) 0 := margin F u v w j hh
  have hl (i : ℝ) : Ready fun u : ℝ => P i u := by
    simp_rw [hh' i, add_comm i]
    exact plus_poly (ready_marg F 0 n w j) i
  have hr : P x t - P y t - d = 0 :=
    congr_fun
      (GFlow.quiet (f := fun t => P x t - P y t - d) (((hl x).sub (hl y)).sub (Ready.const _))
        (hM.congr fun t => ?_))
      t
  · rw [High.Knobs.torch_sub _ (breathing ..) (breathing ..)]
    exact sub_eq_zero.mp hr
  obtain hv := hx t
  rw [High.Knobs.torch_sub _ (hu ..) (hu ..)] at hv
  rw [← hv]
  unfold P
  rw [High.Knobs.torch_sub _ (hu ..) (breathing ..), High.Knobs.torch_sub _ (hu ..) (breathing ..)]
  abel
end YM.WilsonMS.BetaValue
