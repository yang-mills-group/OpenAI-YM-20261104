import YM.WilsonMS.Stencil.Transport
/-!
# Trading midpoint sampled links for holonomy of a smooth family

Model variable smooth continuum fields. For each n build a single field on the
whole continuum: corrections at positive spacing order. Work centre-locally
near EACH `(0,x)`, no uniform analyticity radius assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Paths
open Function Filter Set MeasureTheory
open Analysis Tensor Curves TaylorRules TPath Source
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
local notation "I" => unitInterval
local notation "C" => Gauge.Color G

abbrev Family (G : Gauge) :=
  Axis → ℝ × E4 → G.Color

def Flow (B : Family G) :=
  ∀ i, ContDiff ℝ ∞ (B i)
variable {A : Axis → E4 → C} {B : Family G} {k : ℕ} {m : Axis} {y : E4}

def bridge (m : Axis) (x : ℝ × E4) (s : ℝ) :=
  x.2 + x.1 • ((s - 1 / 2) • basis m)

def heat (B : Family G) (m : Axis) (x : (ℝ × E4) × ℝ) :=
  x.1.1 • B m (x.1.1, bridge m x.1 x.2)

lemma heat_s (h : Flow B) (m : Axis) : ContDiff ℝ ∞ (heat B m) := by
  unfold heat
  refine (contDiff_fst.comp contDiff_fst).smul ((h m).comp (f := fun x => _) ?_)
  unfold bridge
  fun_prop

lemma heat_f (h : Flow B) (v : I) : ContDiffAt ℝ (↑k) (heat B m) ((0, y), v.val) :=
  ((heat_s h _).of_le (WithTop.coe_le_coe.mpr (show (k : ℕ∞) ≤ ⊤ from le_top))).contDiffAt

lemma heat_line (h : Flow B) (x : ℝ × E4) : ContDiff ℝ 1 (fun i => heat B m (x, i)) :=
  ((heat_s h _).of_le (by simp)).comp (by fun_prop)

lemma heat_zero (s : ℝ) : heat B m ((0, y), s) = 0 :=
  zero_smul _ _

def endLink (B : Family G) (m : Axis) (x : ℝ × E4) :=
  track (G := G) (fun t => heat B m (x, t)) 1

def logLink (B : Family G) (m : Axis) (x : ℝ × E4) :=
  G.plog (G.mat (endLink B m x))

lemma zero_U (h : Flow B) : along I (heat B m) (0, y) = 0 :=
  ContinuousMap.ext fun v =>
    (path_val (n := 0) (fun s hs => heat_f h ⟨s, hs⟩) v).trans (heat_zero v.val)

lemma profile (h : Flow B) :
    Agree k (0, y) (G.mat ∘ endLink B m) (TPath.step (TPath.injection G) ∘ along I (heat B m)) :=
  TPath.comparison (fun v hv => heat_f h ⟨v, hv⟩) (fun v _ => heat_zero v) (heat_line h)

lemma identity (h : Flow B) : G.mat (endLink B m (0, y)) = 1 := by
  rw [show G.mat (endLink B m (0, y)) = TPath.step (TPath.injection G) (along I (heat B m) (0, y))
      from Agree.value (profile (k := 0) h),
    zero_U h, TPath.step_zero]

lemma loglink (h : Flow B) : Agree k (0, y) (logLink B m) (TPath.logarithm G ∘ along I (heat B m)) :=
  (profile (m := m) h).apply_smooth (u := G.plog)
    (by
      simp only [Function.comp_apply, zero_U h, step_zero]
      exact G.plog_diff.of_le le_top)

lemma loglink_zero (h : Flow B) : logLink B m (0, y) = 0 := by rw [logLink, identity h, G.plog_one]

lemma in_chart (h : Flow B) : (G.lieExp ∘ logLink B m) =ᶠ[𝓝 (0, y)] endLink B m := by
  have hv :=
    (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr
      (profile (m := m) (y := y) (k := 0) h).smooth.continuousAt
  have hp := identity (m := m) (y := y) h
  have he : Tendsto (endLink B m) (𝓝 (0, y)) (𝓝 1) := by
    rw [← G.mat_injective (hp.trans G.mat_one.symm)]
    exact hv
  exact he.eventually G.plog_right

abbrev feed (f : E4 → C) (x : ℝ × E4) :=
  x.1 • f x.2

abbrev Matches (A : Axis → E4 → C) (B : Family G) (k : ℕ) : Prop :=
  ∀ m y, Agree k 0 (fun t => feed (A m) (t, y)) (fun t => logLink B m (t, y))

def oneHeat (B : Family G) (m : Axis) (x : E4) (z : ℝ × ℝ) :=
  heat B m ((z.1, x), z.2)

def TraceH (B : Family G) (m : Axis) (x : E4) (t : ℝ) :=
  along I (oneHeat B m x) t

lemma traceH_s (h : Flow B) : ContDiffAt ℝ (↑k) (TraceH B m y) 0 :=
  Curves.contDiff_along fun s hs =>
    (heat_f (B := B) (m := m) (y := y) (k := k) h ⟨s, hs⟩).comp (f := fun x : ℝ × ℝ =>
      ((x.1, y), x.2)) _ (by fun_prop)

lemma traceH_form : (TraceH B m y) = fun t : ℝ => along I (heat B m) (t, y) :=
  rfl

lemma traceH_pt (h : Flow B) (s : I) : ContDiffAt ℝ (↑k) (oneHeat B m y) (0, s.val) :=
  (heat_f (B := B) (m := m) (y := y) (k := k) h s).comp (f := fun x : ℝ × ℝ => ((x.1, y), x.2)) _
    (by fun_prop)

lemma sampled_log (h : Flow B) :
    Agree k 0 (fun t => logLink B m (t, y)) (TPath.logarithm G ∘ TraceH B m y) :=
  (Agree.refl (show ContDiffAt ℝ (↑k) (fun t : ℝ => (t, y)) 0 from (by fun_prop))).comp (loglink h)

lemma begin_wave (h : Flow B) (m : Axis) (x : E4) :
    Agree 1 0 (fun t : ℝ => t • B m (0, x)) (fun t => logLink B m (t, x)) := by
  let g := TraceH B m x
  have hg : g 0 = 0 := zero_U h
  have he := sampled_log (k := 1) (m := m) (y := x) h
  have hp : deriv (logarithm G ∘ g) 0 = B m (0, x) := by
    have hv : deriv g 0 = ContinuousMap.const I (B m (0, x)) := by
      apply ContinuousMap.ext
      intro t
      have ht :=
        path_jet (k := 1) (p := (0 : ℝ)) (S := I) (f := oneHeat B m x)
          (fun v hv => traceH_pt h ⟨v, hv⟩) t 1
      change iteratedDeriv 1 g 0 t = iteratedDeriv 1 (fun v : ℝ => oneHeat B m x (v, t.val)) 0 at ht
      rw [iteratedDeriv_one, iteratedDeriv_one] at ht
      rw [ht]
      unfold oneHeat heat
      let f (v : ℝ) := B m (v, bridge m (v, x) t.val)
      have hb : DifferentiableAt ℝ f 0 :=
        ((h m).differentiable (by simp) _).comp (f := fun v => (v, bridge m (v, x) t.val)) _
          (by
            unfold bridge
            fun_prop)
      change _ = B m (0, x)
      have hi : HasDerivAt (fun v => v • f v) (B m (0, x)) 0 := by
        have ht := (hasDerivAt_id' (0 : ℝ)).smul hb.hasDerivAt
        apply HasDerivAt.congr_deriv (f := fun v => v • f v) ht (?_)
        simp [f, bridge]
      exact hi.deriv
    have hi : HasFDerivAt (logarithm G) _ (g 0) :=
      ((show ContDiffAt ℝ ω (logarithm G) (g 0) from
              (by
                rw [hg]
                exact chartable G)).differentiableAt
          (by simp)).hasFDerivAt
    rw [(hi.comp_hasDerivAt _
          (show HasDerivAt g (deriv g 0) 0 from
            ((show ContDiffAt ℝ (↑(1 : ℕ)) g 0 from traceH_s h).differentiableAt
                (by simp)).hasDerivAt)).deriv,
      hg, hv, log_const]
  refine Agree.trans (g := logarithm G ∘ g) (Agree.line (by fun_prop) he.smooth' ?_) he.symm
  intro i hi
  interval_cases i
  · simp only [iteratedDeriv_zero, comp_apply, zero_smul, hg, log_zero]
  simp only [iteratedDeriv_one, hp]
  exact (Eq.trans ((hasDerivAt_id' (0 : ℝ)).smul_const (B m (0, x))).deriv (one_smul ..))
end YM.WilsonMS.Paths
