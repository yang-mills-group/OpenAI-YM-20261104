import YM.WilsonMS.Stencil.LateMotion
import YM.Source.ODE
/-!
# Transport in path germs

Right multiplication sign. We use the analytic resolvent on a neighborhood
of zero curve. `track` always lies in G, see `Source.Hol.pipes` and its
chart local existence. `step` extends endpoint to continuous path input
only as a **matrix** expression. Compare it conditionally, with ODE on [0,1].
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.TPath
open Function Filter Set MeasureTheory
open TaylorRules Source
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "I" => unitInterval

abbrev clamp :=
  Set.projIcc (0 : ℝ) 1 zero_le_one

lemma clamp_id {t : ℝ} (h : t ∈ I) : (clamp t).val = t := by
  unfold clamp
  rw [Set.projIcc_of_mem _ h]

section Volterra

variable (E) [CompleteSpace E] in
def primitive : C(I, E) →L[ℝ] C(I, E) := by
  have hi (U : C(I, E)) (a b : ℝ) : IntervalIntegrable (fun s => U (clamp s)) volume a b :=
    (U.continuous.comp continuous_projIcc).intervalIntegrable a b
  let L : C(I, E) →ₗ[ℝ] C(I, E) :=
    { toFun
        U :=
        ⟨fun t => ∫ s : ℝ in 0..(t : ℝ), U (clamp s),
          (intervalIntegral.continuous_primitive (hi U) 0).comp continuous_subtype_val⟩
      map_add' U V := ContinuousMap.ext fun t => intervalIntegral.integral_add (hi U 0 t) (hi V 0 t)
      map_smul' c
        U := ContinuousMap.ext fun t => intervalIntegral.integral_smul c (fun s => U (clamp s)) }
  refine L.mkContinuous 1 fun U => ?_
  rw [one_mul]
  refine (ContinuousMap.norm_le (L U) (norm_nonneg U)).mpr fun t => ?_
  calc
    _ ≤ ‖U‖ * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (f := fun s => U (clamp s))
        (fun _ _ => U.norm_coe_le_norm _)
    _ ≤ _ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg U) t.property.2
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {R : Type} [NormedRing R]
  [NormedAlgebra ℝ R] [CompleteSpace R] (M : P →L[ℝ] R)

def matrixU : C(I, P) →L[ℝ] C(I, R) := by
  let L : C(I, P) →ₗ[ℝ] C(I, R) :=
    { toFun U := ⟨fun i => M (U i), M.continuous.comp U.continuous⟩
      map_add' U V := ContinuousMap.ext fun i => map_add M (U i) (V i)
      map_smul' c U := ContinuousMap.ext fun i => map_smul M c (U i) }
  exact
    L.mkContinuous ‖M‖ fun U =>
      (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr fun i =>
        (M.le_opNorm (U i)).trans (mul_le_mul_of_nonneg_left (U.norm_coe_le_norm i) (norm_nonneg _))

def volterra : C(I, P) →L[ℝ] (C(I, R) →L[ℝ] C(I, R)) :=
  ((ContinuousLinearMap.compL ℝ C(I, R) _ _) (primitive R)).comp
    ((ContinuousLinearMap.mul ℝ C(I, R)).flip.comp (matrixU M))

def propagator {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F →L[ℝ] F) (e : F)
    (v : E) : F :=
  Ring.inverse (1 - A v) e
section
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (A : E →L[ℝ] F →L[ℝ] F)
  (e : F)

omit [CompleteSpace F] in
lemma prop_zero : propagator A e 0 = e := by simp [propagator]

lemma prop_germ : AnalyticAt ℝ (propagator A e) 0 := by
  have he : AnalyticAt ℝ (fun B : F →L[ℝ] F => Ring.inverse (1 - B)) (A 0) := by
    rw [map_zero]
    exact analyticAt_inverse_one_sub ℝ _
  exact ((ContinuousLinearMap.apply ℝ F e).analyticAt _).comp (he.comp (A.analyticAt _))

lemma has_inverse : ∀ᶠ U in 𝓝 (0 : E), IsUnit (1 - A U) := by
  have he : Tendsto A (𝓝 0) (𝓝 0) := by simpa only [map_zero] using A.continuous.tendsto 0
  filter_upwards [he.eventually (Metric.ball_mem_nhds 0 one_pos)] with v hv
  exact isUnit_one_sub_of_norm_lt_one (show ‖A v‖ < 1 by simpa using hv)

lemma prop_eq : propagator A e =ᶠ[𝓝 0] fun v => e + A v (propagator A e v) := by
  filter_upwards [has_inverse A] with v hv
  have he : (1 - A v) (propagator A e v) = e := by
    unfold propagator
    rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hv]
    rfl
  exact sub_eq_iff_eq_add.mp he

lemma prop_diff : HasFDerivAt (propagator A e) (A.flip e) 0 := by
  let D := (prop_germ A e).differentiableAt
  have ht :=
    ((hasFDerivAt_const e (0 : E)).add (A.hasFDerivAt.clm_apply D.hasFDerivAt)).congr_of_eventuallyEq
      (prop_eq A e)
  simpa [prop_zero] using ht
end

def run (U : C(I, P)) : C(I, R) :=
  propagator (volterra M) 1 U

omit [CompleteSpace R] in
lemma runs_zero : run M 0 = 1 := by
  exact prop_zero (volterra M) 1

lemma analytic : AnalyticAt ℝ (run M) 0 :=
  prop_germ _ _

lemma solvable : ∀ᶠ U in 𝓝 (0 : C(I, P)), IsUnit (1 - volterra M U) :=
  has_inverse _

/-- Compare any solution with restricted [0,1] heat. -/
structure Follow (U : ℝ → R) (A : C(I, P)) : Prop where
  init : U 0 = 1
  lift : ∀ t : I, HasDerivAt U (U t * M (A t)) (t : ℝ)

lemma hits {U : ℝ → R} {A : C(I, P)} (h : Follow M U A) (he : IsUnit (1 - volterra M A)) (t : I) :
    run M A t = U t := by
  have hc : Continuous (fun t : I => U t) :=
    continuous_iff_continuousAt.mpr fun t =>
      (h.lift t).continuousAt.comp continuous_subtype_val.continuousAt
  let v : C(I, R) := ⟨fun t => U t, hc⟩
  suffices hu : (1 - volterra M A) v = 1
    by
    suffices hx : run M A = v from congr_arg (fun F : C(I, R) => F t) hx
    unfold run propagator
    rw [← hu]
    rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ he]
    rfl
  refine ContinuousMap.ext fun t => ?_
  change U (t : ℝ) - (∫ s : ℝ in 0..(t : ℝ), U (clamp s).val * M (A (clamp s))) = 1
  let f (s : ℝ) := U (clamp s).val * M (A (clamp s))
  have hh (s : ℝ) (hx : s ∈ uIcc 0 (t : ℝ)) : HasDerivAt U (f s) s := by
    have hp : s ∈ I := by
      rw [uIcc_of_le t.property.1] at hx
      exact ⟨hx.1, hx.2.trans t.property.2⟩
    have ht : HasDerivAt U (f s) ((clamp s).val) := h.lift _
    rwa [clamp_id hp] at ht
  have ht : IntervalIntegrable f volume 0 (t : ℝ) :=
    Continuous.intervalIntegrable
      ((hc.comp continuous_projIcc).mul (M.continuous.comp (A.continuous.comp continuous_projIcc))) ..
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hh ht, h.init]
  abel

def step (U : C(I, P)) :=
  run M U 1

lemma analyt_step : ContDiffAt ℝ ω (step M) 0 :=
  (ContinuousMap.evalCLM ℝ (1 : I) (M := R)).contDiff.contDiffAt.comp (f := run M) 0
    (analytic M).contDiffAt

omit [CompleteSpace R] in
lemma step_zero : step M 0 = 1 :=
  congr_arg (fun F : C(I, R) => F 1) (runs_zero M)

lemma step_const (x : P) : fderiv ℝ (step M) 0 (ContinuousMap.const I x) = M x := by
  have hk := prop_diff (volterra M) (1 : C(I, R))
  have hh := (ContinuousMap.evalCLM ℝ (1 : I) (M := R)).hasFDerivAt.comp (f := run M) _ hk
  rw [show fderiv ℝ (step M) 0 = _ from hh.fderiv]
  change (∫ s : ℝ in 0..1, 1 * M x) = _
  simp
end Volterra
variable (G : Gauge)

abbrev injection :=
  G.colorMat.toContinuousLinearMap
local notation "C" => Gauge.Color G
local notation "R" => Gauge.Mat G

def logarithm (U : C(I, C)) :=
  G.plog (step (injection G) U)

lemma chartable : ContDiffAt ℝ ω (logarithm G) 0 :=
  ContDiffAt.comp 0 (f := step (injection G)) (g := G.plog)
    (by
      rw [step_zero]
      exact G.plog_diff)
    (analyt_step (injection G))

lemma log_zero : logarithm G 0 = 0 := by rw [logarithm, step_zero, G.plog_one]

lemma log_deriv (x : C) : fderiv ℝ G.plog 1 (G.colorMat x) = x := by
  let R' := G.mat ∘ G.lieExp
  have ht : ContDiffAt ℝ ω G.plog (R' 0) := by
    simp only [R', comp_apply, G.mat_lieExp_zero, G.mat_one]
    exact G.plog_diff
  have he : HasFDerivAt id _ (0 : C) :=
    ((ht.differentiableAt (by simp)).hasFDerivAt.comp (f := R') _
          G.expDiff_zero).congr_of_eventuallyEq
      (show id =ᶠ[𝓝 0] G.plog ∘ R' from Filter.EventuallyEq.symm G.plog_left)
  have hv := congr_arg (fun (F : C →L[ℝ] C) => F x) (he.unique (hasFDerivAt_id _))
  simp only [R', comp_apply, G.mat_lieExp_zero, G.mat_one] at hv
  exact hv

lemma log_const (x : C) : fderiv ℝ (logarithm G) 0 (ContinuousMap.const I x) = x := by
  have ht : ContDiffAt ℝ ω G.plog (step (injection G) 0) := by
    rw [step_zero]
    exact G.plog_diff
  change fderiv ℝ (G.plog ∘ step (injection G)) _ _ = _
  rw [fderiv_comp _ (ht.differentiableAt (by simp))
      ((analyt_step (injection G)).differentiableAt (by simp)),
    step_zero, ContinuousLinearMap.comp_apply, step_const (injection G) x]
  exact log_deriv G x

section family
variable {G : Gauge} {n : ℕ} {p : E} {f : E × ℝ → G.Color}

theorem reaches (h : ∀ i ∈ I, ContDiffAt ℝ (↑n) f (p, i)) (h0 : ∀ i ∈ I, f (p, i) = 0)
    (U : E → ℝ → G.Mat) (hu : ∀ᶠ x in 𝓝 p, Follow (injection G) (U x) (Curves.along I f x)) :
    (fun x => U x 1) =ᶠ[𝓝 p] step (injection G) ∘ Curves.along I f := by
  have he : Curves.along I f p = 0 :=
    ContinuousMap.ext fun t => (Curves.path_val h t).trans (h0 _ t.property)
  have ht : Tendsto (Curves.along I f) (𝓝 p) (𝓝 0) := he ▸ (Curves.contDiff_along h).continuousAt
  filter_upwards [hu, ht.eventually (solvable (injection G))] with x hx hi
  exact (hits (injection G) hx hi 1).symm

def track (f : ℝ → G.Color) : ℝ → G.El :=
  if h : ContDiff ℝ 1 f then (Hol.pipes h).choose else fun _ => 1

lemma tracks {f : ℝ → G.Color} (h : ContDiff ℝ 1 f) : SolvesLink (track f) f := by
  rw [track, dif_pos h]
  exact (Hol.pipes h).choose_spec

lemma track_form {g : ℝ → G.El} {f : ℝ → G.Color} (h : ContDiff ℝ 1 f) (hp : SolvesLink g f) :
    g = track f :=
  hp.unique (tracks h)

lemma track_end (h : ∀ i ∈ I, ContDiffAt ℝ (↑n) f (p, i)) (h0 : ∀ i ∈ I, f (p, i) = 0)
    (ht : ∀ x : E, ContDiff ℝ 1 (fun t => f (x, t))) :
    (fun x => G.mat (track (fun i => f (x, i)) 1)) =ᶠ[𝓝 p] step (injection G) ∘ Curves.along I f := by
  refine reaches h h0 (fun x t => G.mat (track (fun i => f (x, i)) t)) ?_
  filter_upwards [Curves.remain_on h] with x hx
  refine ⟨by rw [(tracks (ht x)).1, G.mat_one], fun i => ?_⟩
  rw [hx]
  exact (tracks (ht x)).2 _

lemma comparison (h : ∀ i ∈ I, ContDiffAt ℝ (↑n) f (p, i)) (h0 : ∀ i ∈ I, f (p, i) = 0)
    (ht : ∀ x : E, ContDiff ℝ 1 (fun t => f (x, t))) :
    Agree n p (fun x => G.mat (track (fun i => f (x, i)) 1))
      (step (injection G) ∘ Curves.along I f) := by
  have he : Curves.along I f p = 0 :=
    ContinuousMap.ext fun t => (Curves.path_val h t).trans (h0 _ t.property)
  refine
    (Agree.of_event (track_end h h0 ht).symm (ContDiffAt.comp _ ?_ (Curves.contDiff_along h))).symm
  rw [he]
  exact (analyt_step (injection G)).of_le le_top
end family
end YM.WilsonMS.TPath
