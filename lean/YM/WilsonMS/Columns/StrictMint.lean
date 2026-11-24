import YM.WilsonMS.Columns.LoopRanks
import YM.WilsonMS.Stencil.LateMotion
/-!
# Keeping highest rank clear of MS pole subtractions

All dim continuations, all positions. Use absolute Taylor grading only where
applicative `kPrice`, and unprojected row on top rank only. Especially,
do NOT pass jet vanishing through arbitrary pointwise limits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.StrictMint
open MS Function Filter Set Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
  _root_.YM.MS.Shine
open Hem Mell Logarithm Pearl Train Signal Book Convolve Garment.Wave Garment.Wick Dock LoopRank
open scoped Topology ContDiff Interval
variable {G : Gauge} {h k i m r n : ℕ} {V W X : Mob G}

def EmptyH (r k : ℕ) (F : Mob G) : Prop :=
  ∀ (j : ℕ) (l : Legs (Shore G j)),
    l.length = r → Tendsto (fun t => plow (-(k : ℂ)) t F j l) atBot (𝓝 0)

def emptyT (r k : ℕ) (F : Mob G) : Prop :=
  ∀ i ≤ k, ∀ j (l : Legs (Shore G j)), l.length = r → Tad F i j l = 0

lemma bareLen (hv : ∀ j (l : Legs (Shore G j)), l.length = r → V j l = 0) : EmptyH r k V := by
  intro j l hl
  unfold plow
  simp_rw [show ∀ t, V j (sr t l) = 0 from fun t =>
      hv j (sr t l) (show (sr t l).length = r by rw [sr, List.length_map, hl]),
    mul_zero]
  exact tendsto_const_nhds

lemma addH (hv : EmptyH r k V) (hx : EmptyH r k X) : EmptyH r k (V + X) := by
  intro m l hl
  simp_rw [← cert, map_add]
  simpa only [zero_add] using! (hv m l hl).add (hx m l hl)

lemma scaleH (c : ℂ) (hv : EmptyH r k V) : EmptyH r k (c • V) := by
  intro m l hl
  simp_rw [← cert, map_smul]
  simpa only [smul_zero] using! (hv m l hl).const_smul c

lemma sumH {I : Type} {F : I → Mob G} (s : Finset I) (hp : ∀ i ∈ s, EmptyH r k (F i)) :
    EmptyH r k (∑ i ∈ s, F i) := by
  classical
    induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty]
    exact bareLen (fun _ _ _ => rfl)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact addH (hp i (by simp)) (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))

private lemma wipeH (hp : ∀ i < n, ∀ j (l : Legs (Shore G j)), l.length = r → Tad V i j l = 0) (m : ℕ)
    (l : Legs (Shore G m)) (he : l.length = r) (s : ℝ) (z : ℂ) : wood n z s V m l = plow z s V m l := by
  unfold wood plow
  rw [show Hem.clear n V m (sr s l) = V m (sr s l) from ?_]
  have hℓ : (sr s l).length = r := by rw [sr, List.length_map, he]
  unfold Hem.clear
  rw [Pi.sub_apply, Pi.sub_apply, haze, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_zero,
    sub_zero]
  exact fun i hi => hp i (mem_range.mp hi) m _ hℓ

lemma firstT (he : kPrice V) (hp : EmptyH r k V) : emptyT r k V := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro m l hl
    have ht := ray_white he i m l
    apply tendsto_nhds_unique ht
    simp_rw [wipeH (n := i) (V := V) (fun i' hi' => ih i' hi' (hi'.le.trans hi)) m l hl]
    rcases lt_or_eq_of_le hi with hx | rfl
    swap
    exact hp m l hl
    let f (t : ℝ) := plow (-(k : ℂ)) t V
    let a : ℂ := (k : ℂ) - (i : ℂ)
    have he' : 0 < a.re := (by simp [a, hx])
    simp_rw [show ∀ t : ℝ, plow (-(i : ℂ)) t V = amount a t • f t from fun t => by
        rw [show -(i : ℂ) = -(k : ℂ) + a from
            (by
              unfold a
              ring),
          Alps.shift] ]
    simpa only [smul_zero] using! (x_scale0 he').smul (hp m l hl)

lemma from_first (hv : kPrice V) (hp : emptyT r k V) : EmptyH r k V := by
  intro m l he
  simp_rw [← wipeH (n := k + 1) (V := V) (fun i hi => hp i (by omega)) m l he]
  exact wood_lim hv (show 0 < (-(k : ℂ)).re + ↑(k + 1 : ℕ) from by simp) m l

private lemma amount_d {f : ℝ → ℂ} (hp : ContDiff ℝ ∞ f) (a : ℂ) (k : ℕ) :
    reading k (Bench.Forest.loadC f a) = (a + k) * reading k f := by
  have ht : ContDiffAt ℝ ∞ (deriv f) 0 := by
    change ContDiffAt ℝ ∞ (Analysis.D 1 f) 0
    exact Analysis.dSmooth hp.contDiffAt _ (by simp)
  have hv (x : ℝ) : Bench.Forest.loadC f a x = a * f x + x ^ 1 • deriv f x := by
    unfold Bench.Forest.loadC
    rw [pow_one, show x • deriv f x = fderiv ℝ f x (x • (1 : ℝ)) from Eq.symm (map_smul ..)]
    rw [smul_eq_mul, mul_one]
  have hF : ContDiff ℝ ∞ (fun x : ℝ => x ^ 1 • deriv f x) := by
    refine (contDiff_id.pow _).smul (contDiff_iff_contDiffAt.mpr ?_)
    intro x
    exact Analysis.dSmooth (hp.contDiffAt (x := x)) _ (by simp)
  rw [funext hv, read_add (contDiff_const.mul hp) hF, read_const]
  unfold reading
  rw [TaylorRules.power_bill (contDiffAt_infty.mp ht _)]
  cases k with
  | zero => simp
  | succ k =>
    rw [if_pos (by omega), Nat.choose_one_right]
    rw [show k + 1 - 1 = k from rfl, ← iteratedDeriv_succ']
    simp only [Nat.factorial_one, Nat.cast_one, one_smul, ← Nat.cast_smul_eq_nsmul ℂ,
      Complex.real_smul, smul_eq_mul]
    ring

lemma jet_burn (h : kPrice V) (i : ℕ) (x : ℂ) : Tad (burn x V) i = (x + i) • Tad V i := by
  funext j l
  by_cases hx : mass l ≤ (i : ℤ)
  swap
  · rw [t_exc (not_le.mp hx), Pi.smul_apply, Pi.smul_apply, t_exc (not_le.mp hx), smul_zero]
  let v := ((i : ℤ) - mass l).toNat
  have he : mass l + v = i := by
    unfold v
    omega
  rw [t_bud _ he, Pi.smul_apply, Pi.smul_apply, t_bud _ he]
  change reading v (fieldVal (burn x V j) (ray l)) = _
  rw [bump h, amount_d ((h j ℝ (ray l)).smooth ())]
  congr 1
  rw [add_assoc, mass, ray_dim, show (fieldDim wfield l : ℂ) + v = i from by exact_mod_cast he]

variable {J : Flats G} {c : ℤ} {b : Bool} {p : ℤ}

abbrev Watch (h r : ℕ) (F : Flats G) : Prop :=
  ∀ ℓ, ∀ᶠ i in dotty, EmptyH r h (F ℓ i)

lemma listens (hp : Coal b h p c J) (ht : Watch h r J) : Watch h r (wheels J h) := by
  obtain ⟨h0, hX, _⟩ := scooter hp.eye hp.force
  intro ℓ
  have hP := ((clockMoon hX).toast ℓ).price
  have hM := ((clockMoon hp.eye).toast ℓ).price
  by_cases hv : ℓ = 0
  · subst ℓ
    rw [loopy]
    rw [loopy] at hP
    simp only [Bless, if_true, add_zero, vampV] at *
    exact Eventually.of_forall fun i j l _ => frame_lim j l
  filter_upwards [h0, hP, hM, ht ℓ, vamp_room h ℓ (Nat.pos_of_ne_zero hv)] with i hi hY hV he hw
  have hh := burn_unique (hi ℓ) hY
  apply from_first hY
  intro l hl m u hu
  have hk : (vamp i h ℓ) + l ≠ 0 := hw l (Nat.lt_succ_of_le hl)
  have hz := firstT hV he l hl m u hu
  rw [hh, jet_burn hY, Pi.smul_apply, Pi.smul_apply] at hz
  exact smul_eq_zero.mp hz |>.resolve_left hk

lemma plow_walk (hv : EmptyH r k V) (s : ℝ) (a : ℂ) : EmptyH r k (plow a s V) := by
  let q : ℂ := -(k : ℂ)
  have he : plow a s V = amount (a - q) s • plow q s V := by
    nth_rw 1 [show a = q + (a - q) from Eq.symm (add_sub_cancel ..)]
    exact Alps.shift ..
  rw [he]
  apply scaleH
  intro m l hl
  have hh := (hv m l hl).comp (tendsto_atBot_add_const_right atBot s tendsto_id)
  change Tendsto (fun t => plow q t (plow q s V) m l) _ _
  simp_rw [snow]
  exact hh

lemma parade_rank (ht : Watch k r J) (s y : ℝ) (n : ℕ) :
    ∀ᶠ i in dotty, EmptyH r k (Parade J n y s i) := by
  rw [Page J.support (by rfl)]
  filter_upwards [eventually_all_finset J.support |>.mpr (fun i hi => ht i)] with i hi
  rw [Finset.sum_apply]
  exact sumH _ fun j hj => scaleH _ (plow_walk (hi j hj) s _)

variable {f : Coat G}

lemma hop_lift (h : Lift f X) (n : ℕ) : Lift (fun i => Tad (f i) n) (Tad X n) := by
  obtain ⟨g, r, hr, h, Ht, rfl⟩ := h
  exact
    Lift.congr (Lift.trim (tad_hol _ h n) hr) (Ht.mono fun _ hi => congr_arg (fun V => Tad V n) hi)

lemma hop_pick (h : Pick n f X) (j : ℕ) : Pick n (fun i => Tad (f i) j) (Tad X j) := by
  induction n generalizing f with
  | zero => exact hop_lift h j
  | succ n ih =>
    obtain ⟨V, H, H0⟩ := h
    refine ⟨_, hop_lift H j, Pick.congr (ih H0) ?_⟩
    filter_upwards [Live.price (f := f) ⟨_, H⟩] with i hi
    unfold slip
    rw [t_pose, t_minus hi (Lift.price H)]

lemma pick_reads {v : Legs (Shore G m)} (h : Pick n f X) (hp : ∀ᶠ i in dotty, f i m v = 0) :
    X m v = 0 := by
  induction n generalizing f with
  | zero =>
    exact
      tendsto_nhds_unique (Lift.wind h m v)
        (Tendsto.congr' (hp.mono (fun _ hi => hi.symm)) tendsto_const_nhds)
  | succ n ih =>
    obtain ⟨V, H, hq⟩ := h
    have hi :=
      tendsto_nhds_unique (Lift.wind H m v)
        (Tendsto.congr' (hp.mono (fun _ hi => hi.symm)) tendsto_const_nhds)
    apply ih hq
    filter_upwards [hp] with k hk
    unfold slip
    rw [Pi.smul_apply, Pi.smul_apply, Pi.sub_apply, Pi.sub_apply, hi, hk, sub_zero, smul_zero]

lemma observes (h : Pick n f X) (hp : ∀ᶠ i in dotty, EmptyH r k (f i)) : EmptyH r k X := by
  apply from_first h.price
  intro j hj m l hl
  exact
    pick_reads (hop_pick h j) ((hp.and h.live.price).mono fun _ ht => firstT ht.2 ht.1 _ hj _ _ hl)

end YM.WilsonMS.StrictMint
