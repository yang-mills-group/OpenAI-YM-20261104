import YM.MSbar.TreeOPE.Answer

/-! Uniform Taylor expansion in the radial variable of a smooth kernel
on a compact family of shapes, and uniqueness of its one-sided
power-series coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OPETreeCompact
open Function Set Filter Asymptotics
open scoped Classical BigOperators ContDiff Topology

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

def axial (f : ℝ × A → ℂ) : ℕ → ℝ × A → ℂ
  | 0 => f
  | k+1 => fun z => fderiv ℝ (axial f k) z (1,0)

theorem axial_smooth {f : ℝ × A → ℂ} {z : ℝ × A} (hf : ContDiffAt ℝ ∞ f z) (k : ℕ) :
    ContDiffAt ℝ ∞ (axial f k) z := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    exact ((ContinuousLinearMap.apply ℝ ℂ ((1:ℝ),(0:A))).contDiff).contDiffAt.comp z
      (ih.fderiv_right (m := ∞) (by simp))

def coefficient (f : ℝ × A → ℂ) (k : ℕ) (x : A) : ℂ :=
  (k.factorial : ℂ)⁻¹ * axial f k (0,x)

theorem coefficient_smooth {f : ℝ × A → ℂ} {x : A} (hf : ContDiffAt ℝ ∞ f (0,x)) (k : ℕ) :
    ContDiffAt ℝ ∞ (coefficient f k) x :=
  contDiffAt_const.mul ((axial_smooth hf k).comp x (contDiffAt_const.prodMk contDiffAt_id))

variable {U : Set (ℝ × A)} (hU : IsOpen U) {f : ℝ × A → ℂ}
    (hf : ∀ z ∈ U, ContDiffAt ℝ ∞ f z)
include hU hf

theorem slice_derivative (k : ℕ) (s : ℝ) (x : A) (hs : (s,x) ∈ U) :
    iteratedDeriv k (fun t => f (t,x)) s = axial f k (s,x) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    have he : (fun t => iteratedDeriv k (fun u => f (u,x)) t) =ᶠ[𝓝 s]
        fun t => axial f k (t,x) := by
      apply ((continuous_id.prodMk continuous_const).continuousAt.eventually
        (hU.mem_nhds hs)).mono
      exact fun t ht => ih t ht
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (((axial_smooth (hf _ hs) k).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))).deriv

/-- The constant and positive radius window are shared by every point
of the given compact set, at each prescribed Taylor degree. -/
theorem uniform_taylor (K : Set A) (hK : IsCompact K) (h0 : ∀ x ∈ K, (0,x) ∈ U) (H : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ x ∈ K,
      (r,x) ∈ U ∧
        ‖f (r,x) - ∑ k ∈ Finset.range (H+1), (r:ℂ)^k * coefficient f k x‖ ≤ C*r^(H+1) := by
  have hstart : ({0} : Set ℝ) ×ˢ K ⊆ U := by
    rintro ⟨s,x⟩ ⟨hs,hx⟩
    have : s = 0 := mem_singleton_iff.mp hs
    subst s
    exact h0 x hx
  obtain ⟨I,V,hI,_,hI0,hV,hUV⟩ := generalized_tube_lemma isCompact_singleton hK hU hstart
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds (hI0 (mem_singleton 0)))
  let ε := δ/2
  have hε : 0 < ε := half_pos hδ
  let slab := Set.Icc (0:ℝ) ε ×ˢ K
  have hslab : slab ⊆ U := by
    rintro ⟨s,x⟩ ⟨hs,hx⟩
    refine hUV ⟨hball ?_,hV hx⟩
    rw [Metric.mem_ball,Real.dist_eq, sub_zero,abs_of_nonneg hs.1]
    dsimp [ε] at hs
    linarith [hs.2]
  have hcompact : IsCompact slab := isCompact_Icc.prod hK
  obtain ⟨B,hB⟩ := hcompact.exists_bound_of_continuousOn
    (f := axial f (H+1)) (fun z hz => (axial_smooth (hf _ (hslab hz)) _).continuousAt.continuousWithinAt)
  refine ⟨max 0 (B/(H.factorial:ℝ)),le_max_left ..,?_⟩
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds]
    with r hr hrε x hx
  have hr' : 0 < r := hr
  let g := fun t : ℝ => f (t,x)
  have hi (t : ℝ) (ht : t ∈ Icc (0:ℝ) r) : (t,x) ∈ slab :=
    ⟨⟨ht.1,ht.2.trans hrε.le⟩,hx⟩
  have hg (t : ℝ) (ht : t ∈ Icc (0:ℝ) r) : ContDiffAt ℝ ∞ g t :=
    (hf _ (hslab (hi t ht))).comp t (contDiffAt_id.prodMk contDiffAt_const)
  have hd (k : ℕ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) r) :
      iteratedDerivWithin k g (Icc 0 r) t = axial f k (t,x) :=
    (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hr')
      ((hg t ht).of_le (WithTop.coe_le_coe.mpr le_top)) ht).trans
        (slice_derivative hU hf k t x (hslab (hi t ht)))
  have hT := taylor_mean_remainder_bound (a := 0) (b := r) (x := r) (n := H) (f := g)
    (C := B) hr'.le (fun t ht => ((hg t ht).of_le (by exact_mod_cast
      (WithTop.coe_le_coe.mpr le_top : (↑(H+1 : ℕ∞) : WithTop ℕ∞) ≤ ∞))).contDiffWithinAt)
    (right_mem_Icc.mpr hr'.le) (fun t ht => (hd (H+1) t ht).symm ▸ hB (t,x) (hi t ht))
  have hTaylor : taylorWithinEval g H (Icc 0 r) 0 r =
      ∑ k ∈ Finset.range (H+1), (r:ℂ)^k * coefficient f k x := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [hd k 0 (left_mem_Icc.mpr hr'.le)]
    simp only [coefficient, sub_zero, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_pow]
    ring
  rw [hTaylor, sub_zero] at hT
  refine ⟨hslab (hi r (right_mem_Icc.mpr hr'.le)),hT.trans ?_⟩
  calc
    B*r^(H+1)/(H.factorial:ℝ) = (B/(H.factorial:ℝ))*r^(H+1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right 0 _) (pow_nonneg hr'.le _)

omit hU hf in
theorem leading_zero (c : ℂ) (k : ℕ)
    (h : (fun r : ℝ => (r:ℂ)^k*c) =O[𝓝[>] 0] (fun r : ℝ => r^(k+1))) : c = 0 := by
  obtain ⟨B,_,hb⟩ := h.exists_nonneg
  have hs : ∀ᶠ r in 𝓝[>] (0:ℝ), ‖c‖ ≤ B*r := by
    filter_upwards [hb.bound,self_mem_nhdsWithin] with r hr hp
    have hp' : 0 < r := hp
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hp'.le,
      Real.norm_of_nonneg (pow_nonneg hp'.le _),pow_succ] at hr
    exact (le_of_mul_le_mul_left (by nlinarith only [hr] : r^k * ‖c‖ ≤ r^k * (B*r))
      (pow_pos hp' k))
  have ht : Tendsto (fun r : ℝ => B*r) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using
      (show Tendsto (fun r : ℝ => B*r) (𝓝 0) (𝓝 (B*(0:ℝ))) from
        tendsto_const_nhds.mul tendsto_id)
  exact norm_eq_zero.mp (le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds
    (ht.mono_left nhdsWithin_le_nhds) hs) (norm_nonneg _))

omit hU hf in
theorem unique (g : ℝ → ℂ) (a b : ℕ → ℂ)
    (ha : ∀ H, (fun r : ℝ => g r-∑ k ∈ Finset.range (H+1), (r:ℂ)^k*a k)
      =O[𝓝[>] 0] (fun r : ℝ => r^(H+1)))
    (hb : ∀ H, (fun r : ℝ => g r-∑ k ∈ Finset.range (H+1), (r:ℂ)^k*b k)
      =O[𝓝[>] 0] (fun r : ℝ => r^(H+1))) : a = b := by
  funext H
  induction H using Nat.strong_induction_on with
  | h H ih =>
    have he (r : ℝ) :
        (g r-∑ k ∈ Finset.range (H+1), (r:ℂ)^k*b k) -
        (g r-∑ k ∈ Finset.range (H+1), (r:ℂ)^k*a k) = (r:ℂ)^H*(a H-b H) := by
      have hl : ∑ k ∈ Finset.range H, (r:ℂ)^k*a k = ∑ k ∈ Finset.range H, (r:ℂ)^k*b k :=
        Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_range.mp hk)]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hl]
      ring
    apply sub_eq_zero.mp
    apply leading_zero _ H
    exact ((hb H).sub (ha H)).congr_left (fun r => he r)

end YM.Integration.OPETreeCompact
