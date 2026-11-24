import YM.MS.ScaleForest.Quotients

/-!
# One explicit loop: doing the scale integral

For use on specific subgraphs. A single page-one force with a regular `W`
dependence in z. We compute its pole, local replacement, and the *finite*
coefficient (at the retained cutoff), including the first continued jet of
one of the Taylor terms. Thus other continuations away from z=0 could matter
even there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest

open Set Filter MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave
open scoped Topology ContDiff

variable {G : Gauge} {W : Coat G} {h n : ℕ} {b : Bool} {r : ℤ} {X Y J : Flats G}
variable (hW : Lift W (W 0))

abbrev pageOne (W : Coat G) : Flats G := Finsupp.single 1 W

theorem integrate_single (h j : ℕ) (W : Coat G) : integratePages h (Finsupp.single j W) =
    Finsupp.single j (fun z : ℂ => scaleIntegral z h j (W z)) := by
  ext1 i; rw [integrate_each]
  by_cases he : i=j
  · subst j; simp
  simp [Ne.symm he]
  rfl

/-- Taylor summands with degrees j < n. -/
def lowerTaylor (n h : ℕ) (W : Coat G) (z : ℂ) := cPos n (vamp z h 1) (W z)

/-- The regular part PRIOR to expanding the top Taylor quotient. -/
def ordinary (h : ℕ) (W : Coat G) (z : ℂ) := progress (h+1) (vamp z h 1) (W z) + lowerTaylor h h W z

/-- The tensor of the divergent Taylor term. Retain it as a REGULATED
tensor, not constant in z. -/
def highTensor (h : ℕ) (W : Coat G) (z : ℂ) := (-(2⁻¹ : ℂ)) • Tad (W z) h

/-- The actual added pole vertex in our z Laurent convention. -/
def taylorPole (h : ℕ) (W : Coat G) : Coat G := Ice 1 (- highTensor h W 0)

/-- The renormalized finite value of this integration at mass and length
parameters `y` and `s` (both logarithmic). The `ruby ... 1` reads the first
Taylor coefficient (NOT degree or coupling order 1) in the dimensional
regulator. -/
def oneLoopFinite (h : ℕ) (W : Coat G) (s y : ℝ) : Mob G :=
  plow (-(h:ℂ)) s (ordinary h W 0) +
    (ruby (highTensor h W) 1 + (↑((y+s) * (-2)) : ℂ) • highTensor h W 0)

theorem Taylor_lift {F : Mob G} (hW : Lift W F) (n : ℕ) : Lift (fun z => Tad (W z) n) (Tad F n) := by
  obtain ⟨g,R,hr,hU,hz,rfl⟩ := hW
  exact Lift.congr (Lift.trim (tad_hol g hU n) hr) (hz.mono fun z hz => congr_arg (fun F => Tad F n) hz)

include hW

theorem small_lift (hp : n ≤ h) : Lift (lowerTaylor n h W) (lowerTaylor n h W 0) := by
  induction n with
  | zero =>
    rw [show lowerTaylor 0 h W=0 from funext fun _=> by simp [lowerTaylor,cPos]]
    exact Lift.zero
  | succ n ih =>
    obtain ⟨R,hR,hx⟩ := Vamp_m (n:=h) (j:=n) (by omega) 1
    let c (z : ℂ) := (vamp z h 1 + n)⁻¹
    have H : Lift (fun z => c z • Tad (W z) n) (c 0 • Tad (W 0) n) :=
      Lift.high (Taylor_lift hW n) (x:=c) (fun i hi => ((vampF h 1 _ i hi).add_const (n:ℂ)).inv (hx i hi)) hR
    rw [show lowerTaylor (n+1) h W= lowerTaylor n h W + fun i => c i • Tad (W i) n from ?_]
    · exact Lift.add (ih (by omega)) H
    funext i
    exact Finset.sum_range_succ ..

theorem prog_lift (h : ℕ) : Lift (fun z => progress (h+1) (vamp z h 1) (W z))
      (progress (h+1) (vamp 0 h 1) (W 0)) := by
  obtain ⟨R,hR,hx⟩ := vamp_fit h 1
  obtain ⟨g,S,hS,hg,hU,hg0⟩ := hW
  rw [← hg0]
  refine Lift.congr (Lift.trim (prog_hol (R:=min S R) (a:=1/2) (by positivity)
    (fun i hi => hx i (Metric.ball_subset_ball (min_le_right ..) hi)) (vampF h 1 _)
    (hg.mono (Metric.ball_subset_ball (min_le_left ..)))) (lt_min hS hR)) ?_
  filter_upwards [hU] with i hi
  simp only [hi]

theorem ordinary_lift (h : ℕ) : Lift (ordinary h W) (ordinary h W 0) :=
  Lift.add (prog_lift hW h) (small_lift hW (le_refl h))

theorem high_lift (h : ℕ) : Lift (highTensor h W) (highTensor h W 0) :=
  Lift.static (Taylor_lift hW h) _

theorem pole_local (h : ℕ) : Count (taylorPole h W) h := by
  intro z
  exact (((Home.tad (Lift.price hW)).smul _).neg).smul _

theorem one_loop_germ (h : ℕ) :
    ∀ᶠ z in dotty, scaleIntegral z h 1 (W z) = ordinary h W z + z⁻¹ • highTensor h W z := by
  filter_upwards [uv_limit (ell:=1) (h:=h) (mer.uLive ⟨_,hW⟩) (by simp), dotty_non] with z hz ht
  have he : (vamp z h 1 + h)⁻¹ = z⁻¹ * (-(2⁻¹:ℂ)) := by rw [(Vamp_high (n:=h) (by decide) z ht).1]; simp
  rw [hz.1,Bless,ordinary,highTensor,lowerTaylor,cPos,cPos, if_neg (one_ne_zero), Finset.sum_range_succ,
    he,mul_smul,add_assoc]

omit hW in
theorem weight_forest (y : ℝ) (D : Set ℂ) : Forest D (fun z => Pearl.weight z 1 y) := by
  intro z _; simp_rw [cubic]; fun_prop

theorem weight_here (h : ℕ) (y : ℝ) : Lift (fun z => Pearl.weight z 1 y • highTensor h W z) (highTensor h W 0) := by
  have ht := Lift.high (high_lift hW h) (weight_forest y (disc 1)) zero_lt_one
  simp only [cubic,mul_zero, Complex.exp_zero,one_smul] at ht
  simp_rw [cubic]
  exact ht

theorem simple_expansion (hX : Pact X (pageOne W)) (h : ℕ) :
    ∀ᶠ z in dotty, ∀ y s,
      Parade (integratePages h X + collapsed (taylorPole h W)) h y s z =
        Pearl.weight z 1 (y+s) • plow (-(h:ℂ)) s (ordinary h W z) +
          slip (fun z => Pearl.weight z 1 (y+s) • highTensor h W z) (highTensor h W 0) z := by
  filter_upwards [one_loop_germ hW h, Live.price (show Live W from ⟨_,hW⟩),
    took (integratePages_congr h hX)] with z hz ht hU
  intro y s
  rw [page_add,Pi.add_apply,pureP _ (pole_local hW h), treaty z hU h y s]
  have he := (Home.tad ht (n:=h)).smul (-(2⁻¹:ℂ)) s
  unfold pageOne
  rw [integrate_single,page_sl,hz,ew]
  simp only [slip,smul_sub,taylorPole,Ice,pow_one,← cert,map_add,map_smul]
  simp_rw [cert,show plow (-(h:ℂ)) s (highTensor h W z) = highTensor h W z from he, smul_neg]
  rw [smul_add, smul_comm _ z⁻¹]; abel

/-- Laurent slope used even *after* constant-value pole subtraction. -/
theorem first_jet (h : ℕ) (y : ℝ) : Pick 1 (fun z => Pearl.weight z 1 y • highTensor h W z)
    (ruby (highTensor h W) 1 + (↑(y * (-2)) : ℂ) • highTensor h W 0) := by
  have ht := Stars (n:=1) (weight_forest y (disc 1)) zero_lt_one
    (fun i => Rub (show Live (highTensor h W) from ⟨_,high_lift hW h⟩) i)
  simp_rw [chem] at ht
  simp only [Finset.sum_range_succ,Nat.sub_self] at ht
  rw [show ruby (highTensor h W) 0 = _ from (chosen (n:=0) (F:= highTensor h W 0) (high_lift hW h)).symm] at ht
  simp only [ley,gNat] at ht
  norm_num at ht
  push_cast; rw [mul_neg, neg_smul]; exact ht

theorem slope_value (h : ℕ) (y : ℝ) :
    Lift (slip (fun z => Pearl.weight z 1 y • highTensor h W z) (highTensor h W 0))
      (ruby (highTensor h W) 1 + (↑(y * (-2)) : ℂ) • highTensor h W 0) := by
  obtain ⟨F,hF,hQ⟩ := first_jet hW h y
  rw [Lift.unique hF (weight_here hW h y)] at hQ
  exact hQ

theorem simple_finite (hX : Pact X (pageOne W)) (h : ℕ) (s y : ℝ) :
    Lift (Parade (integratePages h X + collapsed (taylorPole h W)) h y s) (oneLoopFinite h W s y) := by
  have hp : Lift (fun z => Pearl.weight z 1 (y+s) • plow (-(h:ℂ)) s (ordinary h W z))
      (plow (-(h:ℂ)) s (ordinary h W 0)) := by
    have ht := Lift.high (Lift.plowX (ordinary_lift hW h) s (-(h:ℂ))) (weight_forest (y+s) (disc 1)) zero_lt_one
    simp only [cubic,mul_zero, Complex.exp_zero,one_smul] at ht
    simp_rw [cubic]
    exact ht
  exact Lift.congr (Lift.add hp (slope_value hW h (y+s)))
    ((simple_expansion hW hX h).mono fun x hx => (hx y s).symm)

theorem simple_pole_rule (hX : Pact X (pageOne W)) (hc : Coal b h 0 r X) :
    counterterm (integratePages h X) = taylorPole h W ∧
      ∀ y s, Lift (Parade (integratePages h X + collapsed (counterterm (integratePages h X))) h y s)
        (oneLoopFinite h W s y) := by
  obtain ⟨he,hS⟩ := integrate_sewable (Sewable.mk hc.eye hc.force)
  have hE := ct_unique (fun y s => (show Live (Parade (integratePages h X + collapsed (taylorPole h W)) h y s) from
    ⟨_, simple_finite hW hX h s y⟩)) (pole_local hW h) (iceC _ _ zero_lt_one) hS he hc.real
  rw [←hE]
  exact ⟨rfl,fun y s=> simple_finite hW hX h s y⟩

end YM.MS.ScaleForest
