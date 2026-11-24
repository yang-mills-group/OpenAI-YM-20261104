import YM.MSbar.Pact.Motion
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Haar gauge motion in the log chart

Haar weight (anchor units) not assumed constant. Check its covariance under the local
flow at a link. Use the established exponential-chart identity and transform the comparison
by the adjoint preserving colors. Enough to support analytic germs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Pact
open Function Set Filter MeasureTheory Topology Gauge Origin Push Precision
open scoped BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}

private lemma reachBump (u k g : G.El) : ∀ᶠ z in 𝓝 u, Loops.delta (k*u*g) (k*z*g)=G.adjoint k (Loops.delta u z) := by
  have he : Tendsto (Loops.delta u) (𝓝 u) (𝓝 0) := by
    unfold Loops.delta
    have hs : Tendsto (fun x : G.El => G.mat (x*u⁻¹)) (𝓝 u) (𝓝 1) := by simpa using! ((G.continuous_mat.comp (continuous_id.mul continuous_const)).tendsto u : Tendsto (fun x => G.mat (x*u⁻¹)) (𝓝 u) _)
    rw [← plog_one]; exact G.plog_diff.continuousAt.tendsto.comp hs
  have hs := ((G.adjoint k).toContinuousLinearMap.continuous.tendsto 0).comp he; rw [map_zero] at hs
  filter_upwards [Loops.bump_delta u,hs.eventually (Loops.delta_bump (k*u*g))] with z h j
  rw [←show Loops.bump (k*u*g) (G.adjoint k (Loops.delta u z))=k*z*g from (Loops.bump_transform u k g _).trans (by rw [h])]; exact j
lemma iso_abs (k : G.El) : |((G.adjoint k).toContinuousLinearMap).det|=1 := by
  let e : G.Color →ₗᵢ[ℝ] G.Color := { G.adjoint k with norm_map' := G.norm_adjoint k }
  rw [show ((G.adjoint k).toContinuousLinearMap).det=e.toLinearMap.det from rfl, ←LinearMap.normDet_eq_abs_det, LinearIsometry.normDet_eq_one]
lemma abs_comp (L F : G.Color →L[ℝ] G.Color) : |(L.comp F).det|=|L.det| * |F.det| := by unfold ContinuousLinearMap.det; rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, abs_mul]
variable {P : ChartRatio G}
lemma aperture {T : G.Color→G.Color} {x : G.Color} (hP : LocalRatio P) (hx : x∈Metric.ball 0 P.radius) (t : T x∈ Metric.ball 0 P.radius) (f : DifferentiableAt ℝ T x) (k g : G.El)
    (h : ∀ᶠ a in 𝓝 x,G.lieExp (T a)=k*G.lieExp a*g) : P.J (T x) * |(fderiv ℝ T x).det|=P.J x := by
  let D := fun u v : G.Color => Loops.delta (G.lieExp u) (G.lieExp v)
  have hi y : Eager (D y) y := Loops.delta_diff contDiffAt_const G.exp_jet.contDiffAt rfl
  let L : G.Color→L[ℝ] G.Color := (G.adjoint k).toContinuousLinearMap
  have he : (D (T x)) ∘ T=ᶠ[𝓝 x] L ∘ D x := by
    filter_upwards [h,(G.lieExp_cont.tendsto x).eventually (reachBump (G.lieExp x) k g)] with a u v; unfold D; simp only [comp_apply, u,h.self_of_nhds]; exact v
  replace he := EventuallyEq.fderiv_eq (𝕜:=ℝ) he
  rw [fderiv_comp _ ((hi _).differentiableAt (by simp)) f, fderiv_comp _ L.differentiableAt ((hi x).differentiableAt (by simp)), L.fderiv] at he
  rw [← Loops.exp_delta_det hP hx, ← Loops.exp_delta_det hP t,←abs_comp];
  change |((fderiv ℝ (D (T x)) (T x)).comp (fderiv ℝ T x)).det|=_
  rw [he,abs_comp, show |L.det|=1 from iso_abs _,one_mul]

def routeLog (c d : G.Color) (t : ℝ) (x : G.Color) := leaplog c d x t
lemma log_ready (c d : G.Color) {x : G.Color} (h : Eager G.plog (phi x)) : Eager (uncurry (routeLog c d)) (0,x) := by
   simp only [routeLog,leaplog_at,uncurry_def]; refine ContDiffAt.comp (g:=G.plog) _ ?_ ?_
   · simp only [neg_zero,zero_smul,phi_start,mul_one,one_mul]; exact h
   refine ((phi_ready.contDiffAt.comp (f:=fun z : ℝ×G.Color => -(z.1) • c) _ (by fun_prop)).mul
          (phi_ready.contDiffAt.comp _ contDiffAt_snd)).mul (phi_ready.contDiffAt.comp (f:=fun z : ℝ×G.Color => z.1 • d) _ (by fun_prop))

private lemma vantage (c d : G.Color) {x t} (h : ∀ᶠ y in 𝓝 (leap c d t x), G.lieExp (G.plog (G.mat y))=y) :
    ∀ᶠ z in 𝓝 x, G.lieExp (routeLog c d t z) = G.lieExp ((-t) • c)* G.lieExp z * G.lieExp (t • d) := by apply ((continuous_const.mul G.lieExp_cont).mul continuous_const).continuousAt (x:=x)|>.tendsto.eventually (p:=fun y:G.El => G.lieExp (G.plog (G.mat y))=y); exact h

private def opening (x : G.El) := ∀ᶠ y in 𝓝 x,G.lieExp (G.plog (G.mat y))=y
private lemma surrounds : ∀ᶠ x : G.Color in 𝓝 0, ∀ᶠ y in 𝓝 (G.lieExp x), opening y := by
  apply (G.lieExp_cont.tendsto 0).eventually (p:=fun u : G.El => ∀ᶠ y in 𝓝 u, opening y)
  rw [G.mat_lieExp_zero]
  exact eventually_eventually_nhds.mpr (eventually_eventually_nhds.mpr G.plog_right)
private lemma entrances (c d : G.Color) (x : G.Color) (h : ∀ᶠ y in 𝓝 (G.lieExp x), opening y) : ∀ᶠ t in 𝓝 0, opening (leap c d t x) := by
  have E : Continuous (fun t : ℝ => leap c d t x) := by unfold leap; exact ((G.lieExp_cont.comp (continuous_id.neg.smul continuous_const)).mul continuous_const).mul (G.lieExp_cont.comp (continuous_id.smul continuous_const))
  apply (E.tendsto 0).eventually; rw [leap_zero]; exact h
private lemma rooms (c d : G.Color) {x} (_ : LocalRatio P) (h : x∈Metric.ball 0 P.radius)
    (v : HasDerivAt (leaplog c d x) (onlink c d x) 0) (p : leaplog c d x 0=x) : ∀ᶠ t in 𝓝 0, routeLog c d t x∈Metric.ball 0 P.radius := by
  have hp : ∀ᶠ t in 𝓝 0, leaplog c d x t∈Metric.ball 0 P.radius := v.continuousAt.eventually (Metric.isOpen_ball.mem_nhds (show leaplog c d x 0∈ Metric.ball 0 P.radius by rw [p]; exact h))
  exact hp
private lemma progress (c d : G.Color) {x} (h : Eager G.plog (phi x)) : ∀ᶠ t in 𝓝 0,DifferentiableAt ℝ (routeLog c d t) x := by
  have hh : Continuous (fun t : ℝ => (t,x)) := continuous_id.prodMk continuous_const
  have he : ∀ᶠ y in 𝓝 (0,x), Eager (uncurry (routeLog c d)) y := (log_ready c d h).eventually (by simp)
  apply ((hh.tendsto 0).eventually he).mono; intro t U
  exact (U.differentiableAt (by simp)).comp (f:=fun x : G.Color => (t,x)) x (by fun_prop)
lemma turn_preserves (c d : G.Color) (H : LocalRatio P) : ∀ᶠ x in 𝓝 0, ∀ᶠ t in 𝓝 0, P.J (routeLog c d t x) * |(fderiv ℝ (routeLog c d t) x).det|=P.J x := by
  filter_upwards [log_near, surrounds (G:=G), pacing c d, leaplog_start c d, Metric.ball_mem_nhds (0:G.Color) H.patch] with x h T v u z
  filter_upwards [entrances c d x T, rooms c d H z v u,progress c d h] with t U V W
  exact aperture (T:=routeLog c d t) H z V W (G.lieExp ((-t) • c)) (G.lieExp (t • d)) (vantage c d (x:=x) (t:=t) U)

abbrev fjell (P : ChartRatio G) := Real.log ∘ P.J
lemma fjell_origin (H : LocalRatio P) : fjell P 0=0 := by simp [fjell,H.anchored]
lemma fjell_ready (H : LocalRatio P) {x : G.Color} (h : x∈Metric.ball 0 P.radius) : Eager (fjell P) x := (H.germ _ h).log (H.pos _ h |>.ne')
lemma fjell_flat (H : LocalRatio P) (a : G.Color) : fderiv ℝ (fjell P) 0 a=0 := by
  have hi := (fjell_ready H (Metric.mem_ball_self H.patch)).differentiableAt (by simp)
  refine (Push.side (fjell P) hi a).unique (Next.SectorChange.still_even hi ?_ a)
  filter_upwards [Metric.ball_mem_nhds (0:G.Color) H.patch] with x hx; exact congrArg Real.log (Next.SectorChange.ratio_even H hx).symm
end YM.MSBar.Pact
