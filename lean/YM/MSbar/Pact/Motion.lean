import YM.MSbar.Origin.Compact
import YM.LocalH.Chart
import YM.Push.LOOP_COEFFICIENT.Tangent
import YM.Gauge.Casimir

/-!
# At one link, action of the gauge generators

The actual matrix group of the baseline theory, its exponential germ and
its tangent. Matrix norm Frobenius. Whole budget of statements local -- use
only at the zero field projective series. Haar not funded here. Act by **inverse**
group at start of a positively oriented link. Adopt the convention of
Charm in its structure-constant indexing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Pact
open Function Set Filter MeasureTheory Topology Gauge Origin Push Matrix
open scoped BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}

abbrev phi (a : G.Color) := G.mat (G.lieExp a)
lemma phi_ready : ContDiff ℝ ω (phi (G:=G)) := G.exp_jet
@[simp] lemma phi_start : phi (0:G.Color)=1 := by simp [phi]

/-- Infinitesimal coordinate action when the two site parameters are `c,d`. -/
def rise (c d : G.Color) : G.Mat →L[ℝ] G.Mat :=
 ({ toFun m := m * G.colorMat d-G.colorMat c*m
    map_add' m z := by simp only [add_mul, mul_add]; abel
    map_smul' u z := by simp [smul_sub] } : G.Mat→ₗ[ℝ] G.Mat).toContinuousLinearMap
lemma rise_at (c d : G.Color) (x : G.Mat) : rise c d x = x * G.colorMat d-G.colorMat c*x := rfl

def onlink (c d : G.Color) : G.Color→ G.Color := fun x => fderiv ℝ G.plog (phi x) (rise c d (phi x))
lemma onlink_pair_add (c d a b z : G.Color) : onlink (c+d) (a+b) z = onlink c a z+onlink d b z := by
  simp only [onlink,rise_at,map_add,mul_add,add_mul,map_sub]; abel
lemma onlink_smul (c d : G.Color) (u : ℝ) (z : G.Color) : onlink (u • c) (u • d) z=u • onlink c d z := by simp only [onlink,rise_at,map_smul,Matrix.mul_smul,smul_mul,smul_sub,map_sub]
lemma onlink_zero (z : G.Color) : onlink 0 0 z=0 := by simp [onlink,rise_at]
lemma log_near : ∀ᶠ a : G.Color in 𝓝 0,Eager G.plog (phi a) :=
  (G.exp_jet.continuous.continuousAt (x:=0) |>.tendsto).eventually (by simpa using G.plog_diff.eventually (by simp))
lemma unison : ∀ᶠ a : G.Color in 𝓝 0,G.plog (phi a)=a := G.plog_left
private lemma pull_stub {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} {x} {g : F → E} (T : F →L[ℝ] F) (h : Eager f x) (j : Eager g (f x)) : Eager (fun y => fderiv ℝ g (f y) (T (f y))) x :=
       ((j.fderiv_right (m:=ω) (by simp)).comp x h).clm_apply (T.contDiff.contDiffAt.comp x h)
lemma onlink_ready (c d : G.Color) : Eager (onlink c d) 0 := by
  apply pull_stub (rise c d) phi_ready.contDiffAt (by rw [phi_start]; exact G.plog_diff)

def leap (c d : G.Color) (t : ℝ) (x : G.Color) := G.lieExp ((-t) • c)*G.lieExp x*G.lieExp (t • d)
def leaplog (c d : G.Color) (x : G.Color) (t : ℝ) := G.plog (G.mat (leap c d t x))
lemma leap_zero (c d x : G.Color) : leap c d 0 x=G.lieExp x := by simp [leap]
lemma leap_mat (c d x : G.Color) (t : ℝ) : G.mat (leap c d t x)=phi ((-t) • c)*phi x*phi (t • d) := by simp [leap,phi]
lemma leaplog_at (c d x : G.Color) (t : ℝ) : leaplog c d x t=G.plog (phi ((-t) • c)*phi x*phi (t • d)) := by rw [leaplog,leap_mat]

lemma spinout (c : G.Color) : HasDerivAt (fun t : ℝ => phi (t • c)) (G.colorMat c) 0 := by
  have hc : HasDerivAt (fun t : ℝ => t • c) c 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const c
  let F : HasFDerivAt phi G.colorMat.toContinuousLinearMap ((0:ℝ) • c) := by rw [zero_smul]; exact G.expDiff_zero
  exact F.comp_hasDerivAt (0:ℝ) hc
lemma leap_pace (c d x : G.Color) : HasDerivAt (fun t : ℝ => G.mat (leap c d t x)) (rise c d (phi x)) 0 := by
  have he : HasDerivAt (fun t : ℝ => phi ((-t) • c)) (-G.colorMat c) 0 := by simpa [Function.comp_def] using spinout (-c)
  have hh := (he.mul_const (phi x)).mul (spinout d)
  simpa only [leap_mat,rise_at, Pi.mul_apply,zero_smul,phi_start,neg_mul,one_mul,mul_one,neg_zero,add_comm,sub_eq_add_neg] using! hh
lemma leaplog_start (c d : G.Color) : ∀ᶠ x in 𝓝 0, leaplog c d x 0=x := unison.mono fun x h => by rw [leaplog,leap_zero]; exact h
lemma leaped (c d : G.Color) : ∀ᶠ x in 𝓝 0, ∀ᶠ t in 𝓝 0, G.lieExp (leaplog c d x t)=leap c d t x := by
  have hr : ∀ᶠ y in 𝓝 (1:G.El), ∀ᶠ x in 𝓝 y, G.lieExp (G.plog (G.mat x))=x := eventually_eventually_nhds.mpr G.plog_right
  filter_upwards [(G.lieExp_cont.tendsto 0).eventually (by simpa only [mat_lieExp_zero] using hr)] with x hx
  have H : Continuous (fun t : ℝ => leap c d t x) := by unfold leap; exact ((G.lieExp_cont.comp (continuous_id.neg.smul continuous_const)).mul continuous_const).mul (G.lieExp_cont.comp (continuous_id.smul continuous_const))
  exact (H.tendsto 0).eventually (show ∀ᶠ y in 𝓝 (leap c d 0 x),G.lieExp (G.plog (G.mat y))=y by rw [leap_zero]; exact hx)
lemma pacing (c d : G.Color) : ∀ᶠ x in 𝓝 0, HasDerivAt (leaplog c d x) (onlink c d x) 0 := by
  apply log_near.mono; intro a ha
  have h := leap_pace c d a
  exact ((show HasFDerivAt G.plog _ (G.mat (leap c d 0 a)) by rw [leap_zero]; exact (ha.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt (0:ℝ) h) 
lemma inherit (c d : G.Color) : ∀ᶠ a in 𝓝 0,fderiv ℝ phi a (onlink c d a)=rise c d (phi a) := by
  filter_upwards [pacing c d,leaplog_start c d, leaped c d] with x hx z h
  have hu := (phi_ready.differentiable (by simp) _ |>.hasFDerivAt).comp_hasDerivAt (0:ℝ) hx
  rw [z] at hu; exact ((hu.congr_of_eventuallyEq (h.mono (fun i hi => (congrArg G.mat hi).symm))).unique (leap_pace c d x))
lemma anchored : ∀ᶠ x in 𝓝 (0:G.Color), Injective (fderiv ℝ phi x) := by
  filter_upwards [eventually_eventually_nhds.mpr (unison (G:=G)),log_near (G:=G)] with x hx j
  have he : fderiv ℝ (G.plog ∘ phi) x=fderiv ℝ id x := EventuallyEq.fderiv_eq (f:=id) hx
  rw [fderiv_comp _ (j.differentiableAt (by simp)) (phi_ready.differentiable (by simp) _), fderiv_id] at he; intro a b H
  have hu (z) := DFunLike.congr_fun he z; exact (show _=a from hu a).symm.trans ((congrArg (fderiv ℝ G.plog (phi x)) H).trans (hu b))
lemma onlink_start (c d : G.Color) : onlink c d 0=d-c := by
  apply G.colorMat_injective; have he : fderiv ℝ phi (0:G.Color)=G.colorMat.toContinuousLinearMap := G.expDiff_zero.fderiv
  rw [map_sub]; exact (show G.colorMat.toContinuousLinearMap _ =_ by simpa [he,rise_at] using (inherit c d).self_of_nhds)
end YM.MSBar.Pact
