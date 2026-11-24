import YM.SchemeConversionRG11.Foundation.Jet

/-!
# Inversion as *formal* change of coordinate

Even the leading linear coefficient in a chosen coupling must be checked. Do not pick
arbitrary nonlinear kinetic/coupling assumptions here. Also records local injectivity for
changing coordinate jets, allowing both base points to vary (used with regulators).
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Series

open Function Filter Pert.Position
open scoped Topology ContDiff

section Chart
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {x : E}

theorem exists_coordinates (hf : ContDiffAt ℝ ω f x) (hk : (fderiv ℝ f x).IsInvertible) :
    ∃ g : F → E, g (f x) = x ∧ ContDiffAt ℝ ω g (f x) ∧
       (∀ᶠ q in 𝓝 x, g (f q) = q) ∧ (∀ᶠ q in 𝓝 (f x), f (g q) = q) := by
  obtain ⟨L, hL⟩ := hk
  have hF : HasFDerivAt f (L : E →L[ℝ] F) x := by
    rw [hL]; exact (hf.differentiableAt (by simp)).hasFDerivAt
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let A := hf.toOpenPartialHomeomorph f hF pn
  refine ⟨hf.localInverse hF pn, hf.localInverse_apply_image hF pn, hf.to_localInverse hF pn, ?_, ?_⟩
  · filter_upwards [A.open_source.mem_nhds (show x ∈ A.source from
      hf.mem_toOpenPartialHomeomorph_source hF pn)] with y hy
    exact A.left_inv hy
  filter_upwards [A.open_target.mem_nhds (show f x ∈ A.target from
    hf.image_mem_toOpenPartialHomeomorph_target hF pn)] with y hy
  exact A.right_inv hy

/-- One common neighborhood for uniqueness of any finite jet solution. -/
theorem eventually_chart_inj (hf : ContDiffAt ℝ ω f x) (hk : (fderiv ℝ f x).IsInvertible) :
    ∀ᶠ y : E × E in 𝓝 (x,x), ∀ (a b : Series E), a 0 = y.1 → b 0 = y.2 → ∀ p,
      Through p (liftJet f a) (liftJet f b) → Through p a b := by
  obtain ⟨g, -, hd, hleft, -⟩ := exists_coordinates hf hk
  have he : ∀ᶠ y : E in 𝓝 x,
      ContDiffAt ℝ ω f y ∧ ContDiffAt ℝ ω g (f y) ∧ (∀ᶠ z in 𝓝 y, (g ∘ f) z = z) :=
    (hf.eventually (by simp)).and ((hf.continuousAt.tendsto.eventually (hd.eventually (by simp))).and
      (eventually_eventually_nhds.mpr hleft))
  rw [nhds_prod_eq]
  filter_upwards [he.prod_mk he] with y hy
  intro a b ha hb p hab
  have H (t : E) (h : ContDiffAt ℝ ω f t ∧ ContDiffAt ℝ ω g (f t) ∧
         ∀ᶠ z in 𝓝 t, (g ∘ f) z = z) (a : Series E) (ht : a 0 = t) :
         Through p a (liftJet g (liftJet f a)) := by
    obtain ⟨h, hg, hz⟩ := h
    subst t
    have hc := trunc_represents a p
    have hj := (hc.lift h).lift (show ContDiffAt ℝ ω g (liftJet f a 0) from by simpa using hg)
    have hcv := hc.regular.continuousAt.tendsto
    rw [hc.value] at hcv
    exact hc.unique (hj.germ (hcv.eventually hz |>.mono fun i hi ↦ hi.symm))
  exact (H _ hy.1 _ ha).trans ((hab.lift (show ContDiffAt ℝ ω g _ from by
    rw [liftJet_zero, ha]; exact hy.1.2.1)).trans (H _ hy.2 _ hb).symm)
end Chart

/-- Centered, with nonzero tangent. At reporting also need orientation/sector and a
separate quantitative budget. -/
def Good (x : Series ℝ) : Prop := x 0 = 0 ∧ x 1 ≠ 0

variable {x y z w : Series ℝ} {p : ℕ}

/-- The finite two-sided jet inverse calculation. -/
structure Inverts (p : ℕ) (x y : Series ℝ) : Prop where
  centered : x 0 = 0
  base : y 0 = 0
  forward : Through p (subJet x y) parameter
  backward : Through p (subJet y x) parameter

theorem Inverts.symm (h : Inverts p x y) : Inverts p y x :=
  ⟨h.base, h.centered, h.backward, h.forward⟩

theorem Inverts.unique (h : Inverts p x y) (hz : z 0 = 0)
    (th : Through p (subJet x z) parameter) : Through p y z := by
  have hu := (Through.rfl (a := y)).subst_jet th ((subJet_base hz).trans h.centered)
  have hp := h.backward.subst_jet (Through.rfl (a := z)) hz
  rw [subJet_assoc h.centered hz, subJet_id] at hu
  rw [id_subJet hz] at hp
  exact hu.symm.trans hp

theorem Inverts.mono (h : Inverts p x y) {m : ℕ} (hm : m ≤ p) : Inverts m x y :=
  ⟨h.centered, h.base, h.forward.mono hm, h.backward.mono hm⟩

theorem Inverts.congr (h : Inverts p x y) (he : Through p x w) (hy : Through p y z) :
    Inverts p w z :=
  ⟨he.zero.symm.trans h.centered, hy.zero.symm.trans h.base,
    (he.subst_jet hy h.base).symm.trans h.forward, (hy.subst_jet he h.centered).symm.trans h.backward⟩

theorem subJet_tangent (x y : Series ℝ) (hy : y 0 = 0) :
    subJet x y 1 = x 1 * y 1 := by
  have hu := trunc_represents x 1
  have hv := trunc_represents y 1
  have hgy : trunc y 1 0 = 0 := hv.value.trans hy
  rw [← (hu.subJet hv hy).first le_rfl,
    deriv_comp _ (show DifferentiableAt ℝ _ _ from
      (hgy.symm ▸ hu.regular : ContDiffAt ℝ ω _ (trunc y 1 0)).differentiableAt (by simp))
      (hv.regular.differentiableAt (by simp)), hgy, hu.first le_rfl, hv.first le_rfl]

theorem Inverts.tangent (h : Inverts p x y) (hp : 1 ≤ p) : x 1 * y 1 = 1 :=
  (subJet_tangent x y h.base).symm.trans ((h.forward 1 hp).trans parameter_one)

theorem Inverts.good (h : Inverts p x y) (hp : 1 ≤ p) : Good y :=
  ⟨h.base, fun hw ↦ zero_ne_one (by simpa only [hw, mul_zero] using h.tangent hp)⟩

theorem Good.compose (hx : Good x) (hy : Good y) : Good (subJet x y) :=
  ⟨(subJet_base hy.1).trans hx.1, (subJet_tangent x y hy.1) ▸ mul_ne_zero hx.2 hy.2⟩

private theorem scalar_unit (a : ℝ → ℝ) (hr : DifferentiableAt ℝ a 0) (h : deriv a 0 ≠ 0) :
    (fderiv ℝ a 0).IsInvertible := by
  suffices H : Bijective (fderiv ℝ a 0) from ⟨ContinuousLinearEquiv.ofBijective _
    (LinearMap.ker_eq_bot.mpr H.1) (LinearMap.range_eq_top.mpr H.2), by ext; rfl⟩
  have he (y : ℝ) : fderiv ℝ a 0 y = y * deriv a 0 := by
    rw [hr.hasDerivAt.hasFDerivAt.fderiv]
    rfl
  refine ⟨fun y z H ↦ mul_right_cancel₀ h (by simpa only [he] using H), fun y ↦ ?_⟩
  exact ⟨y / deriv a 0, by rw [he, div_mul_cancel₀ _ h]⟩

theorem Good.finite_inverse (hx : Good x) (n : ℕ) : ∃ y, Inverts n x y := by
  let N := max n 1
  have H := trunc_represents x N
  let f := trunc x N
  have hd : f 0 = 0 := H.value.trans hx.1
  have ht : deriv f 0 ≠ 0 := (H.first (le_max_right ..)).trans_ne hx.2
  obtain ⟨g, hv, hg, hl, hr⟩ :=
    exists_coordinates H.regular (scalar_unit f (H.regular.differentiableAt (by simp)) ht)
  change g (f 0) = 0 at hv
  change ContDiffAt ℝ ω g (f 0) at hg
  change ∀ᶠ q in 𝓝 (f 0), f (g q) = q at hr
  rw [hd] at hv hg hr
  have H' : Represents n g (record g) := record_represents hg
  have he := (record_zero_degree g).trans hv
  refine ⟨record g, hx.1, he, ?_, ?_⟩
  · have hu : Represents n id (subJet x (record g)) :=
      ((H.mono (le_max_left ..)).subJet H' he).germ
        (show f ∘ g =ᶠ[𝓝 (0:ℝ)] id from hr).symm
    exact hu.unique (record_represents contDiffAt_id)
  have hu : Represents n id (subJet (record g) x) :=
    (H'.subJet (H.mono (le_max_left ..)) hx.1).germ
      (show g ∘ f =ᶠ[𝓝 (0:ℝ)] id from hl).symm
  exact hu.unique (record_represents contDiffAt_id)

/-- Totalized off legal input. Use via `Good` lemmas. -/
def reversion (x : Series ℝ) : Series ℝ :=
  open scoped Classical in
  if h : Good x then fun i ↦ Classical.choose (h.finite_inverse i) i else 0

theorem Good.reversion_inverts (h : Good x) (p : ℕ) : Inverts p x (reversion x) := by
  let W (j : ℕ) := Classical.choose (h.finite_inverse j)
  have hw (j : ℕ) : Inverts j x (W j) := Classical.choose_spec (h.finite_inverse j)
  apply (hw p).congr Through.rfl
  intro i hi
  exact (by simpa only [reversion, dif_pos h] using
    (((hw p).mono hi).unique (hw i).base (hw i).forward i le_rfl))

theorem Good.left (h : Good x) : subJet (reversion x) x = parameter :=
  funext (fun j ↦ (h.reversion_inverts j).backward j le_rfl)

theorem Good.right (h : Good x) : subJet x (reversion x) = parameter :=
  funext (fun j ↦ (h.reversion_inverts j).forward j le_rfl)

theorem Good.rev (h : Good x) : Good (reversion x) :=
  (h.reversion_inverts 1).good le_rfl

theorem Good.orientation (h : Good x) (hx : 0 < x 1) : 0 < reversion x 1 :=
  pos_of_mul_pos_right ((h.reversion_inverts 1).tangent le_rfl ▸ zero_lt_one) hx.le

theorem Good.involutive (h : Good x) : reversion (reversion x) = x :=
  funext (fun j ↦ (h.rev.reversion_inverts j).unique h.1 ((h.reversion_inverts j).symm.forward) j le_rfl)

theorem Through.reverts (h : Through p x y) (hx : Good x) (hy : Good y) :
    Through p (reversion x) (reversion y) :=
  ((hx.reversion_inverts p).congr h Through.rfl).unique hy.rev.1 (hy.reversion_inverts p).forward

end YM.SchemeConversionRG11.Series
