import YM.Progress.DIRECTED_RECIPE.Normalization
import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundLogs
import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundMoments

/-! A bounded Borel Wilson action tilt survives every original finite regulator kernel at each coarse field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonBoundedActionTilt

open Function Filter MeasureTheory Lattice Wilson RG WilsonLimitConstruction
  PhysicalNext.Repeat.Legato WilsonCouplingTransport
open scoped Topology BigOperators Classical
variable {G : Gauge}

def weight (R : Run G) (N p : ℕ) (Z : Config G (R.family.side N p) → ℝ) (U : Config G (R.family.side N p)) :
    ℝ := Real.exp (-Z U)*bare (R.family.beta N p) U

private theorem scaled (R : Run G) (N p : ℕ) (i : ℕ) (hi : i≤N) (c : ℝ) (V : Config G (R.family.side i p)) :
    carry R.family p N (R.family.path.β N p) (fun U => c*bare (R.family.beta N p) U) i hi V =
      c*(R.family.path.rep N p i).eval V := by
  rw [FundedWilsonBackgroundRun.scale]
  exact congrArg (fun q : Config G (R.family.side i p) → ℝ => c*q V)
    (WilsonCouplingTransport.physical_density R.family R.makes N p hi)

theorem envelope (R : Run G) (N p : ℕ) (Z : Config G (R.family.side N p) → ℝ)
    (hZ : Measurable Z) (q : ℝ) (h : ∀ U, |Z U|≤q) :
    ∀ i (hi : i≤N) V,
    let y := carry R.family p N (R.family.path.β N p) (weight R N p Z) i hi V
    let w := (R.family.path.rep N p i).eval V
    Real.exp (-q)*w ≤ y ∧ y≤Real.exp q*w ∧ 0<y ∧ ‖Real.log (y/w)‖≤q := by
  let C := R.family
  let b := C.beta N p
  let W := weight R N p Z
  have hw := Wilson.bare_integrable (G:=G) (n:=C.side N p) b
  have bound (U : Config G (C.side N p)) : Real.exp (-q)*bare b U≤W U ∧ W U≤Real.exp q*bare b U := by
    have hz := abs_le.mp (h U)
    refine ⟨mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hz.2)) (bare_pos b U).le,?_⟩
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [hz.1])) (bare_pos b U).le
  have hW : Integrable W (prior G _) := (hw.const_mul (Real.exp q)).mono'
    ((hZ.neg.exp.mul (measurable_bare b)).aestronglyMeasurable)
    (ae_of_all _ fun U => by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤W U from mul_nonneg (Real.exp_pos _).le (bare_pos b U).le)]
      exact (bound U).2)
  intro i hi V
  let w := (C.path.rep N p i).eval V
  let y := carry C p N (C.path.β N p) W i hi V
  have hp : 0<w := RG02.Actual.eval_pos R.makes.wilson hi V
  have hlo : Real.exp (-q)*w≤y := by
    rw [←scaled R N p i hi (Real.exp (-q)) V]
    exact FundedWilsonBackgroundLogs.monotone C p N _ _ _ (hw.const_mul _) hW (fun U => (bound U).1) hi V
  have hhi : y≤Real.exp q*w := by
    rw [←scaled R N p i hi (Real.exp q) V]
    exact FundedWilsonBackgroundLogs.monotone C p N _ _ _ hW (hw.const_mul _) (fun U => (bound U).2) hi V
  have hy := (mul_pos (Real.exp_pos _) hp).trans_le hlo
  refine ⟨hlo,hhi,hy,abs_le.mpr ⟨?_,?_⟩⟩
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) ((le_div_iff₀ hp).2 hlo)
  · simpa only [Real.log_exp] using Real.log_le_log (div_pos hy hp) ((div_le_iff₀ hp).2 hhi)

def oscillation (q : ℝ) := max (Real.exp q-1) (1-Real.exp (-q))

theorem oscillation_le {q : ℝ} (hq : 0≤q) (h1 : q≤1) : oscillation q ≤ 2*q := by
  apply max_le
  · have H := Real.abs_exp_sub_one_le (x:=q) (by rwa [abs_of_nonneg hq])
    exact (le_abs_self _).trans (by simpa only [abs_of_nonneg hq] using H)
  · have H := Real.abs_exp_sub_one_le (x := -q) (by rwa [abs_neg,abs_of_nonneg hq])
    have hw : 1-Real.exp (-q) ≤ |Real.exp (-q)-1| := by rw [abs_sub_comm];exact le_abs_self _
    exact hw.trans (by simpa only [abs_neg,abs_of_nonneg hq] using H)

theorem factor {z q : ℝ} (h : |z| ≤ q) : |Real.exp (-z)-1| ≤ oscillation q := by
  have hz := abs_le.mp h
  have hl := Real.exp_le_exp.mpr (neg_le_neg hz.2)
  have hr : Real.exp (-z) ≤ Real.exp q := Real.exp_le_exp.mpr (by linarith only [hz.1])
  refine abs_le.mpr ⟨?_,(sub_le_sub_right hr 1).trans (le_max_left ..)⟩
  have hq : 1-Real.exp (-q) ≤ oscillation q := le_max_right ..
  linarith only [hl,hq]

theorem pointwise (R : Run G) (N p : ℕ) (Z : Config G (R.family.side N p) → ℝ)
    (q : ℝ) (h : ∀ U, |Z U|≤q) (M : ℝ) (hM : 0≤M) (F : Config G (R.family.side N p) → ℂ)
    (hF : ∀ U, ‖F U‖≤M) (U : Config G (R.family.side N p)) :
    ‖(↑(weight R N p Z U-bare (R.family.beta N p) U):ℂ)*F U‖ ≤
      (oscillation q*M)*bare (R.family.beta N p) U := by
  let b := R.family.beta N p
  have hx := factor (h U)
  have he : weight R N p Z U-bare b U = (Real.exp (-Z U)-1)*bare b U := by unfold weight;dsimp only [b];ring
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,he,abs_mul,abs_of_nonneg (bare_pos _ _).le]
  calc
    _ ≤ (|Real.exp (-Z U)-1| * bare b U)*M :=
      mul_le_mul_of_nonneg_left (hF U) (mul_nonneg (abs_nonneg _) (bare_pos _ _).le)
    _ ≤ (oscillation q*bare b U)*M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx (bare_pos _ _).le) hM
    _ = _ := by ring

/-- Absolute signed joint defect, normalized by the original true law at the same coarse field. -/
theorem signed (R : Run G) (N p : ℕ) (Z : Config G (R.family.side N p) → ℝ)
    (q : ℝ) (h : ∀ U, |Z U|≤q) (M : ℝ) (hM : 0≤M)
    (F : Config G (R.family.side N p) → ℂ) (hF : ∀ U, ‖F U‖≤M)
    (i : ℕ) (hi : i≤N) (V : Config G (R.family.side i p)) :
    ‖carry R.family p N (R.family.path.β N p)
      (fun U => (↑(weight R N p Z U-bare (R.family.beta N p) U):ℂ)*F U) i hi V‖ ≤
      (oscillation q*M)*(R.family.path.rep N p i).eval V := by
  let C := R.family
  let b := C.beta N p
  let c := oscillation q*M
  have bound := pointwise R N p Z q h M hM F hF
  exact (FundedWilsonBackgroundRun.dominated C p N _ _ _ ((bare_integrable b).const_mul c) bound hi V).trans_eq
    (scaled R N p i hi c V)

/-- Each authentic finite conditional sends an everywhere positive integrable fine density to one
    which is strictly positive at every coarse field, for arbitrary real kernel couplings. -/
theorem carry_positive (C : Family G) (p N : ℕ) (γ : ℕ → ℝ) (w : Config G (C.side N p) → ℝ)
    (hw : Integrable w (Wilson.prior G _)) (hpos : ∀ U, 0 < w U) (i : ℕ) (hi : i ≤ N) :
    ∀ V, 0 < carry C p N γ w i hi V := by
  induction hi using Nat.decreasingInduction with
  | self => simpa only [WilsonCouplingTransport.top] using hpos
  | of_succ m hm ih =>
    intro V
    rw [WilsonCouplingTransport.step C p N γ w hm]
    let S := C.path.levels.clock.op m p
    let D := carry C p N γ w (m+1) hm
    let b := γ (m+1)
    have hp (U : Config G (C.side (m+1) p)) : 0 < S.density b U V • D U :=
      mul_pos (Progress.DirectedRecipe.density_strict S b (C.path.levels.blocks m p).branches U V) (ih U)
    have hD := WilsonCouplingTransport.integrable C p N γ hw hm
    change 0 < ∫ U, S.density b U V • D U ∂Wilson.prior G _
    apply (integral_pos_iff_support_of_nonneg (fun U => (hp U).le) (S.push_slice (C.path.levels.transition_mass m p b) V D hD)).2
    rw [Set.eq_univ_of_forall (s := (fun U => S.density b U V • D U).support) (fun U => (hp U).ne'),measure_univ]
    simp

def movingWeight {n : Side} (β : ℝ) (Z : Config G n → ℝ) (U : Config G n) : ℝ :=
  Real.exp (-Z U)*bare β U

/-- A freely varied true inverse-square UV action, followed by the literal finite block kernels. -/
theorem integrable_moving {n : Side} (β : ℝ) (Z : Config G n → ℝ) (hZ : Measurable Z)
    (q : ℝ) (ha : ∀ U, |Z U| ≤ q) : Integrable (movingWeight β Z) (Wilson.prior G n) := by
  apply ((bare_integrable (G:=G) (n:=n) β).const_mul (Real.exp q)).mono'
    (hZ.neg.exp.mul (measurable_bare β)).aestronglyMeasurable
  apply ae_of_all
  intro U
  change ‖Real.exp (-Z U)*bare β U‖ ≤ Real.exp q*bare β U
  rw [Real.norm_eq_abs,abs_of_pos (mul_pos (Real.exp_pos _) (bare_pos β U))]
  apply mul_le_mul_of_nonneg_right _ (bare_pos β U).le
  exact Real.exp_le_exp.mpr (by linarith only [(abs_le.mp (ha U)).1])

theorem moving (C : Family G) (p N : ℕ) (γ : ℕ → ℝ) (β : ℝ)
    (Z : Config G (C.side N p) → ℝ) (hZ : Measurable Z) (q : ℝ) (ha : ∀ U, |Z U| ≤ q)
    (i : ℕ) (hi : i ≤ N) (V : Config G (C.side i p)) :
    let w := carry C p N γ (bare β) i hi V
    let y := carry C p N γ (movingWeight β Z) i hi V
    0 < w ∧ 0 < y ∧ Real.exp (-q)*w ≤ y ∧ y ≤ Real.exp q*w ∧ ‖Real.log (y/w)‖ ≤ q := by
  intro w y
  let W := movingWeight β Z
  have h0 := bare_integrable (G:=G) (n:=C.side N p) β
  have bound (U : Config G (C.side N p)) :
      Real.exp (-q)*bare β U ≤ W U ∧ W U ≤ Real.exp q*bare β U := by
    have h := abs_le.mp (ha U)
    refine ⟨mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h.2)) (bare_pos β U).le,?_⟩
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [h.1])) (bare_pos β U).le
  have hW := integrable_moving β Z hZ q ha
  have hw : 0 < w := carry_positive C p N γ (bare β) h0 (bare_pos β) i hi V
  have hlo : Real.exp (-q)*w ≤ y := by
    have h := FundedWilsonBackgroundLogs.monotone C p N γ _ W (h0.const_mul (Real.exp (-q))) hW
      (fun U => (bound U).1) hi V
    rwa [FundedWilsonBackgroundRun.scale] at h
  have hhi : y ≤ Real.exp q*w := by
    have h := FundedWilsonBackgroundLogs.monotone C p N γ W _ hW (h0.const_mul (Real.exp q))
      (fun U => (bound U).2) hi V
    rwa [FundedWilsonBackgroundRun.scale] at h
  have hy : 0 < y := (mul_pos (Real.exp_pos _) hw).trans_le hlo
  have hl : Real.exp (-q) ≤ y/w := (le_div_iff₀ hw).2 hlo
  have hr : y/w ≤ Real.exp q := (div_le_iff₀ hw).2 hhi
  refine ⟨hw,hy,hlo,hhi,?_⟩
  rw [Real.norm_eq_abs,abs_le]
  exact ⟨by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hl,
    by simpa only [Real.log_exp] using Real.log_le_log (div_pos hy hw) hr⟩

private theorem marked_integrable {n : Side} (v : Config G n → ℝ) (hv : Integrable v (Wilson.prior G n))
    (hp : ∀ U, 0 ≤ v U) (hv' : Measurable v) (O : Config G n → ℂ) (hO : Measurable O)
    (M : ℝ) (hM : ∀ U, ‖O U‖ ≤ M) : Integrable (FundedWilsonBackgroundMoments.mark v O) (Wilson.prior G n) := by
  apply (hv.const_mul M).mono' ((Complex.continuous_ofReal.measurable.comp hv').mul hO).aestronglyMeasurable
  apply ae_of_all
  intro U
  change ‖(v U:ℂ)*O U‖ ≤ M*v U
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp U)]
  exact (mul_le_mul_of_nonneg_left (hM U) (hp U)).trans_eq (mul_comm _ _)

private theorem marked_bound (C : Family G) (p N : ℕ) (γ : ℕ → ℝ)
    (v : Config G (C.side N p) → ℝ) (hv : Integrable v (Wilson.prior G _))
    (hp : ∀ U, 0 ≤ v U) (O : Config G (C.side N p) → ℂ) (M : ℝ) (hM : ∀ U, ‖O U‖ ≤ M)
    (i : ℕ) (hi : i ≤ N) (V : Config G (C.side i p)) :
    ‖carry C p N γ (FundedWilsonBackgroundMoments.mark v O) i hi V‖ ≤ M*carry C p N γ v i hi V := by
  have h := FundedWilsonBackgroundRun.dominated C p N γ (FundedWilsonBackgroundMoments.mark v O)
    (fun U => M*v U) (hv.const_mul M) (fun U => by
      rw [FundedWilsonBackgroundMoments.mark,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp U)]
      exact (mul_le_mul_of_nonneg_left (hM U) (hp U)).trans_eq (mul_comm _ _)) hi V
  rwa [FundedWilsonBackgroundRun.scale] at h

/-- The two honest normalized signed readings at the same coarse field for an
arbitrary positive bare coupling and its bounded measurable action correction. -/
theorem normalized (C : Family G) (p N : ℕ) (γ : ℕ → ℝ) (β : ℝ)
    (Z : Config G (C.side N p) → ℝ) (hZ : Measurable Z) (q : ℝ) (hz : ∀ U, |Z U| ≤ q)
    (O : Config G (C.side N p) → ℂ) (hO : Measurable O) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ U, ‖O U‖ ≤ M) (i : ℕ) (hi : i ≤ N) (V : Config G (C.side i p)) :
    let w := carry C p N γ (bare β) i hi V
    let y := carry C p N γ (movingWeight β Z) i hi V
    let a := carry C p N γ (FundedWilsonBackgroundMoments.mark (movingWeight β Z) O) i hi V
    let b := carry C p N γ (FundedWilsonBackgroundMoments.mark (bare β) O) i hi V
    ‖a/(y:ℂ)-b/(w:ℂ)‖ ≤ 2*oscillation q*M := by
  intro w y a b
  let W := movingWeight β Z
  have hW := integrable_moving β Z hZ q hz
  have hw₀ := bare_integrable (G:=G) (n:=C.side N p) β
  have hW₀ (U : Config G (C.side N p)) : 0 ≤ W U := (mul_pos (Real.exp_pos _) (bare_pos β U)).le
  have ab := marked_bound C p N γ W hW hW₀ O M hb i hi V
  have ⟨hw,hy,hlo,hhi,_⟩ := moving C p N γ β Z hZ q hz i hi V
  have hρ : |y/w-1| ≤ oscillation q := by
    refine abs_le.mpr ⟨?_,(sub_le_sub_right ((div_le_iff₀ hw).2 hhi) 1).trans (le_max_left ..)⟩
    have hl := (le_div_iff₀ hw).2 hlo
    have hδ : 1-Real.exp (-q) ≤ oscillation q := le_max_right ..
    linarith only [hl,hδ]
  let Wm := FundedWilsonBackgroundMoments.mark W O
  let bm := FundedWilsonBackgroundMoments.mark (bare β) O
  have im := marked_integrable W hW hW₀ (hZ.neg.exp.mul (measurable_bare β)) O hO M hb
  have ib := marked_integrable (bare β) hw₀ (fun U => (bare_pos β U).le) (measurable_bare β) O hO M hb
  have hD (U : Config G (C.side N p)) : ‖(Wm-bm) U‖ ≤ (oscillation q*M)*bare β U := by
    change ‖(W U:ℂ)*O U-(bare β U:ℂ)*O U‖ ≤ _
    rw [← sub_mul,← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have e : W U-bare β U = (Real.exp (-Z U)-1)*bare β U := by dsimp [W,movingWeight];ring
    rw [e,abs_mul,abs_of_nonneg (bare_pos β U).le]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right (factor (hz U)) (bare_pos β U).le) (hb U)
      (norm_nonneg _) (mul_nonneg ((abs_nonneg _).trans (factor (hz U))) (bare_pos β U).le)).trans_eq (by ring)
  have d := FundedWilsonBackgroundRun.dominated C p N γ (Wm-bm)
    (fun U => (oscillation q*M)*bare β U) (hw₀.const_mul _) hD hi V
  rw [FundedWilsonBackgroundMoments.subtract C p N γ Wm bm im ib hi,
    FundedWilsonBackgroundRun.scale] at d
  have hd : ‖(a-b)/(w:ℂ)‖ ≤ oscillation q*M := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw]
    exact (div_le_iff₀ hw).2 d
  have hA : ‖a/(y:ℂ)‖ ≤ M := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]
    exact (div_le_iff₀ hy).2 ab
  have hR : ‖((y/w-1:ℝ):ℂ)‖ ≤ oscillation q := by rwa [Complex.norm_real,Real.norm_eq_abs]
  have e : a/(y:ℂ)-b/(w:ℂ) = (a-b)/(w:ℂ)-(a/(y:ℂ))*((y/w-1:ℝ):ℂ) := by
    have hY : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show 0<y from hy).ne'
    have cancel : a/(y:ℂ)*((y:ℂ)/(w:ℂ)) = a/(w:ℂ) := by
      rw [← mul_div_assoc,div_mul_cancel₀ _ hY]
    push_cast
    rw [mul_sub,mul_one,cancel,sub_div]
    ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  exact (add_le_add hd (mul_le_mul hA hR (norm_nonneg _) hM)).trans_eq (by ring)

end YM.Integration.WilsonBoundedActionTilt
end
