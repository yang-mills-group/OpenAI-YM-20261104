import YM.WilsonMS.Stencil.CurvatureCovariant
import YM.WilsonMS.Stencil.JOptics
/-!
# Verify Jrad formula at all the nonlinear ranks

Here the same curvature reading as a *real* differential polynomial on a
continuum potential. Identify continuum off-shell test on Wilson stencils
(this file); momentum tensors next.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.PlaneGauge
open Function Filter Set MeasureTheory
open Analysis Tensor Curves TaylorRules TPath Source Paths RGerm JRad Panel
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {A : VectorA G} {W : Paths.Family G} {H : Hol G} {k : ℕ} {v : XSpace.Period}
variable (s : ℝ) (x : E4)

lemma sweep_dir (h : Flow W) (f : AtG G) (hp : ContDiffAt ℝ ∞ f 0) :
    (fun t : ℝ => deriv (fun t : ℝ => f (t • x)) t) =ᶠ[𝓝 0] fun t =>
      PlaneGauge.direction (voiced (RGerm.pull W) s) x f (t • x) := by
  let R (t : ℝ) := t • x
  have ht : Tendsto R (𝓝 0) (𝓝 0) := by
    simpa only [zero_smul, R] using
      (show Continuous (fun t : ℝ => t • x) from (by fun_prop)).tendsto 0
  filter_upwards [ht.eventually ((hp.of_le (m := 1) (by simp)).eventually (by simp)), rayH h x s] with
    t hx hh
  have hD : HasDerivAt R x t := by simpa only [R, one_smul] using! (hasDerivAt_id' t).smul_const x
  change ∑ i : Axis, x i • _ = (0 : G.Color) at hh
  let A := voiced (RGerm.pull W) s
  have he : ∑ i : Axis, x i • dValue A f i (R t) = ∑ i : Axis, x i • D (basis i) f (R t) := by
    unfold dValue
    simp_rw [smul_add, Finset.sum_add_distrib]
    rw [show ∑ i : Axis, x i • (G.ad (A i (R t)) (f (R t))) = 0 from ?_, add_zero]
    change ∑ j : Axis, x j • (LinearMap.flip G.ad (f (R t))) (A j (R t)) = _
    simp_rw [← map_smul, ← map_sum, show ∑ j : Axis, x j • A j (R t) = 0 from hh, map_zero]
  change deriv (f ∘ R) t = ∑ i : Axis, x i • dValue A f i (R t)
  rw [he,
    ((show DifferentiableAt ℝ f (R t) from
            hx.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt
        t hD).deriv]
  unfold D
  simp_rw [← map_smul, ← map_sum]
  rw [show ∑ i : Axis, x i • basis i = x by
      ext
      simp]

lemma reading_word (h : Flow W) (a b : Axis) :
    powers (voiced (RGerm.pull W) s) a b x k 0 =
      iteratedDeriv k (fun t : ℝ => field (voiced (RGerm.pull W) s) a b (t • x)) 0 := by
  let B := voiced (RGerm.pull W) s
  have ht :
    (fun t : ℝ => powers B a b x k (t • x)) =ᶠ[𝓝 0]
      iteratedDeriv k (fun t : ℝ => PlaneGauge.field B a b (t • x)) := by
    induction k with
    | zero => exact EventuallyEq.rfl
    | succ k ih =>
      have hh :=
        sweep_dir s x h (powers B a b x k)
          (powers_s (show Regular B 0 from fun i => pulseS h i) _ _ _)
      simp_rw [powers, iterate_succ_apply']
      rw [iteratedDeriv_succ]
      exact hh.symm.trans ih.deriv
  rw [← ht.eq_of_nhds]
  simp [B]

private lemma d_root (h : Flow W) (i : Axis) :
    ∀ᶠ v : E4 in 𝓝 0,
      ∑ j : Axis, v j • D (basis j) (voiced (RGerm.pull W) s i) v + voiced (RGerm.pull W) s i v =
        ∑ j : Axis, v j • PlaneGauge.field (voiced (RGerm.pull W) s) j i v := by
  let B := voiced (RGerm.pull W) s
  have hs : Regular B 0 := fun i => pulseS h i
  have hp : (fun v : E4 => ∑ j : Axis, v j • B j v) =ᶠ[𝓝 0] 0 :=
    ((continuous_const.prodMk continuous_id).tendsto (0 : E4)).eventually (root_free (a := s) h)
  filter_upwards [hp, hp.fderiv (𝕜 := ℝ),
    eventually_all.mpr (fun j => ((hs j).of_le (m := 1) (by simp)).eventually (by simp))] with v hv hu
    hJ
  let I (j : Axis) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Axis => ℝ) j) ∘L
      (PiLp.continuousLinearEquiv 2 ℝ _).toContinuousLinearMap
  have hd (j : Axis) : DifferentiableAt ℝ (B j) v := (hJ j).differentiableAt one_ne_zero
  have ht (j : Axis) :
    D (basis i) (fun x : E4 => x j • B j x) v = v j • D (basis i) (B j) v + (I j (basis i)) • B j v := by
    have he := DFunLike.congr_fun ((I j).hasFDerivAt.smul ((hd j).hasFDerivAt)).fderiv (basis i)
    exact he
  have hW : B i v + ∑ j : Axis, v j • D (basis i) (B j) v = 0 := by
    have hm := DFunLike.congr_fun hu (basis i)
    rw [fderiv_fun_sum (A := fun j : Axis => fun x : E4 => x j • B j x)
        (fun j _ => DifferentiableAt.smul ((I j).differentiableAt) (hd j))] at hm
    rw [_root_.sum_apply, fderiv_zero] at hm
    change ∑ j : Axis, D (basis i) (fun x : E4 => x j • B j x) v = 0 at hm
    simp_rw [ht, Finset.sum_add_distrib] at hm
    rw [add_comm]
    simpa [I] using hm
  unfold field
  change _ = ∑ j : Axis, v j • (D (basis j) (B i) v - D (basis i) (B j) v + G.ad (B j v) (B i v))
  simp_rw [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [show ∑ j : Axis, v j • G.ad (B j v) (B i v) = 0 from ?_, add_zero]
  · rw [eq_sub_iff_add_eq, add_assoc, hW, add_zero]
  change ∑ j : Axis, v j • (LinearMap.flip G.ad (B i v)) (B j v) = _
  simp_rw [← map_smul, ← map_sum, show ∑ j : Axis, v j • B j v = 0 from hv, map_zero]

variable (i : Axis)

lemma unit_scale (h : Flow W) :
    let B := voiced (RGerm.pull W) s
    (fun t : ℝ => B i (t • x) + t • deriv (fun t : ℝ => B i (t • x)) t) =ᶠ[𝓝 0] fun t =>
      t • ∑ j : Axis, x j • PlaneGauge.field B j i (t • x) := by
  intro B
  let g (t : ℝ) := t • x
  have ht : Tendsto g (𝓝 0) (𝓝 0) := by
    simpa only [zero_smul] using! (show Continuous (fun t : ℝ => t • x) from (by fun_prop)).tendsto 0
  filter_upwards [ht.eventually (d_root s h i),
    ht.eventually (((pulseS (a := s) h i).of_le (m := 1) (by simp)).eventually (by simp))] with t he
    hq
  have hf : DifferentiableAt ℝ (B i) (g t) := hq.differentiableAt one_ne_zero
  have hp : HasDerivAt g x t := by simpa only [one_smul] using! (hasDerivAt_id' t).smul_const x
  have hi : fderiv ℝ (B i) (g t) x = ∑ j : Axis, x j • D (basis j) (B i) (g t) := by
    unfold D
    simp_rw [← map_smul, ← map_sum]
    rw [show ∑ i : Axis, x i • basis i = x by
        ext
        simp]
  change B i (g t) + t • deriv (B i ∘ g) t = _
  rw [(hf.hasFDerivAt.comp_hasDerivAt _ hp).deriv, hi, add_comm]
  rw [Finset.smul_sum, Finset.smul_sum]
  simp_rw [smul_smul]
  exact he

private lemma shift_order {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (h : ContDiffAt ℝ ∞ f 0) :
    iteratedDeriv (k + 1) (fun t : ℝ => t • f t) 0 = (k + 1) • iteratedDeriv k f 0 := by
  rw [show (fun t : ℝ => t • f t) = (fun t : ℝ => t ^ 1 • f t) from (by simp),
    power_bill (contDiffAt_infty.mp h _)]
  simp

/-- ordinary reading (Jrad) at an open axis. -/
def head (A : VectorA G) (x : E4) (i : Axis) (k : ℕ) :=
  JRad.volume k • ∑ a : Axis, x a • powers A a i x k 0

lemma head_at (h : Flow W) : head (voiced W s) x i k = (records h s k).value i x := by
  let A := voiced W s
  let B := voiced (RGerm.pull W) s
  let g (t : ℝ) := t • x
  let f := B i ∘ g
  have hr : Regular B 0 := fun i => pulseS h i
  have hz : g 0 = 0 := zero_smul _ _
  have he : ContDiffAt ℝ ∞ g 0 :=
    (by
      unfold g
      fun_prop)
  let F (j : Axis) := PlaneGauge.field B j i ∘ g
  have hp : ContDiffAt ℝ ∞ f 0 :=
    ContDiffAt.comp _ (f := g) (g := B i)
      (by
        rw [hz]
        exact hr i)
      he
  have ht (j : Axis) : ContDiffAt ℝ ∞ (F j) 0 :=
    ContDiffAt.comp _ (f := g) (g := PlaneGauge.field B j i)
      (by
        rw [hz]
        exact field_s hr j i)
      he
  have hh (j : Axis) : powers A j i x k 0 = iteratedDeriv k (F j) 0 :=
    (at_anchor h j i x k s).symm.trans (reading_word s x h j i)
  have hc := unit_scale s x i h
  have hd : ContDiffAt ℝ ∞ (deriv f) 0 := by exact (Analysis.dSmooth hp (1 : ℝ) (by simp))
  have hv := hc.iteratedDeriv_eq (k + 1)
  change
    iteratedDeriv (k + 1) (f + (fun t : ℝ => t • deriv f t)) 0 =
      iteratedDeriv (k + 1) (fun t : ℝ => t • ∑ j : Axis, x j • F j t) 0 at hv
  rw [iteratedDeriv_add (contDiffAt_infty.mp hp _) (g := fun t : ℝ => t • deriv f t)
      (contDiffAt_infty.mp (contDiffAt_id.smul hd) _),
    shift_order hd, ← iteratedDeriv_succ',
    shift_order
      (show ContDiffAt ℝ ∞ (fun t => ∑ j : Axis, x j • F j t) 0 from
        ContDiffAt.sum fun j _ => (ht j).const_smul _)] at hv
  rw [iteratedDeriv_fun_sum (f := fun j t => x j • F j t)
      (fun j _ => ((contDiffAt_infty.mp (ht j) k).const_smul _))] at hv
  simp_rw [iteratedDeriv_fun_const_smul (contDiffAt_infty.mp (ht _) _), ← hh] at hv
  change
    JRad.volume k • ∑ j : Axis, x j • powers A j i x k 0 =
      Tensor.diagonal (Tensor.coeff (B i) (k + 1) 0) x
  rw [coeff_ray x (contDiffAt_infty.mp (hr i) _)]
  change _ = (((k + 1).factorial : ℝ))⁻¹ • iteratedDeriv (k + 1) f 0
  let w := ∑ j : Axis, x j • powers A j i x k 0
  let u := iteratedDeriv (k + 1) f 0
  change u + (k + 1) • u = (k + 1) • w at hv
  change JRad.volume k • w = (((k + 1).factorial : ℝ))⁻¹ • u
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ] at hv
  push_cast at hv
  rw [show JRad.volume k • w = ((k + 2 : ℝ) * ((k + 1).factorial : ℝ))⁻¹ • (((k : ℝ) + 1) • w) from
      ?_,
    ← hv]
  swap
  · unfold JRad.volume
    rw [smul_smul, Nat.factorial_succ]
    congr 1
    push_cast
    field_simp
  nth_rw 1 [← one_smul ℝ u]
  rw [← add_smul, show 1 + (k + 1 : ℝ) = k + 2 from ?_, smul_smul]
  swap
  · ring
  congr 1
  field_simp
section physical
open Labels

abbrev Probe (G : Gauge) :=
  E4 × Axis × G.ColorIndex

def linear_part (G : Gauge) (n : ℕ) (p : Probe G) : Module.Dual ℝ (Labels.Taylor G n) :=
  JRad.reading G n p.1 p.2.1 p.2.2

lemma spreads (f : Module.Dual ℝ (Labels.Taylor G k)) :
    ∃ x : Probe G →₀ ℝ, x.sum (fun i c => c • linear_part G k i) = f := by
  have hp : Set.range (linear_part G k) = {f | ∃ x a c, f = reading G k x a c} := by
    ext x
    constructor
    rintro ⟨⟨i, a, c⟩, rfl⟩
    exact ⟨i, a, c, rfl⟩
    rintro ⟨i, a, c, rfl⟩
    exact ⟨(i, a, c), rfl⟩
  exact
    Finsupp.mem_span_range_iff_exists_finsupp.mp
      (show f ∈ Submodule.span ℝ _ from by
        rw [hp, JRad.enough]
        exact Submodule.mem_top)

def ray_basis (v : Labels.Key G) : Probe G →₀ ℝ :=
  (spreads (JRad.φ v)).choose

lemma ray_eq (v : Labels.Key G) : (ray_basis v).sum (fun i c => c • linear_part G v.1 i) = JRad.φ v :=
  (spreads _).choose_spec

def moveSlot (G : Gauge) (A : VectorA G) (v : Labels.Key G) : ℂ :=
  (↑((ray_basis v).sum (fun p c => c • (head A p.1 p.2.1 v.1) p.2.2)) : ℂ)

def unread (A : VectorA G) : Labels.Pol G →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval (moveSlot G A)

lemma sent (h : Flow W) (p : Labels.Pol G) : unread (voiced W s) p = Labels.read (records h s) p := by
  let A := voiced W s
  have he (v : Labels.Key G) : moveSlot G A v = coord (records h s) v := by
    unfold moveSlot coord A
    congr 1
    change _ = φ v ((records h s) v.1)
    rw [← ray_eq v]
    unfold Finsupp.sum
    rw [LinearMap.sum_apply (M := Labels.Taylor G v.1) (σ₁₂ := RingHom.id ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [head_at s _ _ h]
    rfl
  unfold unread Labels.read
  rw [show moveSlot G _ = _ from funext he]

lemma Wilson_top {n l : ℕ} (p : Labels.Label G n) (K : XSpace.Survey G H n) (hp : p ∈ Grade (n, l))
    (ht : ∀ i, ContDiff ℝ ∞ (A i)) :
    Agree n 0 (fun t : ℝ => Webs.reader K p.val (coarse A t)) (fun t : ℝ => t ^ n • unread A p.val) := by
  obtain ⟨B, h, hq, H'⟩ := reverse_mean A ht n
  have he : voiced B 0 = A := funext fun i => funext fun x => hq i x
  rw [show unread A p.val = Labels.read (records h 0) p.val from (by rw [← sent (s := 0) h, he])]
  exact radix_jet K hp (fun i y => (H' i y).lower (Nat.le_succ _)) h ht
end physical
end YM.WilsonMS.PlaneGauge
