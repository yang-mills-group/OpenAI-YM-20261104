import YM.Work.A15
import YM.MultipleContact.Fields
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Compact-detector orbit estimates

Keep complete O(4) action on physical fields of every filtration level.
For smoothness of the coefficient prescription we use only continuous
parameter dependence of this representation; it's the *position* variables
we differentiate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov
open Function Set Filter Table MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

attribute [local instance] YM.Work.A15.compact_ortho

-- Scoped, not affecting the underlying construction
scoped instance compactSphere : CompactSpace Ortho := inferInstance -- prop

scoped instance secondSphere : SecondCountableTopology Ortho := by
  haveI : SecondCountableTopology M4 :=
    inferInstanceAs (SecondCountableTopology (Axis → Axis → ℝ))
  exact inferInstanceAs
    (SecondCountableTopology ↥((Matrix.unitaryGroup Axis ℝ : Set M4)))

scoped instance seesSphere : MeasurableSpace Ortho := borel Ortho
scoped instance realSphere : BorelSpace Ortho := ⟨rfl⟩

private def allG : TopologicalSpace.PositiveCompacts Ortho :=
  ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩

def angles : Measure Ortho := Measure.haarMeasure allG

instance haar_angles : angles.IsHaarMeasure := by unfold angles; infer_instance
instance one_angles : IsProbabilityMeasure angles :=
  ⟨@Measure.haarMeasure_self Ortho _ _ _ _ _ allG⟩

variable {G : Gauge} {L : Register G} {S : Table L} {T : Table L} {R : S.Rotation}

lemma continuous_orbit (v : E4) : Continuous fun R : Ortho => Ortho.move R v := by
  have ha : Continuous (fun s : Ortho => s.val) := continuous_subtype_val
  -- coordinate topology
  unfold Ortho.move
  apply (PiLp.continuous_toLp ..).comp
    (show Continuous (fun R:Ortho => WithLp.ofLp (M4.move R.val v)) from ?_)
  apply continuous_pi
  intro k
  change Continuous fun R:Ortho => M4.move R.val v k
  simp_rw [M4.at_coord]
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply (A:=fun _:Axis=>ℝ) j).comp ((continuous_apply k).comp ha)).mul continuous_const

lemma linear_orbit (R : S.Rotation) {P : DiffPlan S} {ρ : S.RealSpin} (H : R.Laws P ρ) (d : ℕ) :
    Continuous fun K => (LinearMap.toContinuousLinearMap (((R.act d K).toLinearMap).restrictScalars ℝ)) :=
  continuous_clm_apply.mpr (fun v => H.spin d v) -- maybe expects ContinuousOn

/-- Expose conjugation as real-linear too, for passing through integrals. -/
def reflectionC (ρ : S.RealSpin) (d : ℕ) : S.Field d →L[ℝ] S.Field d :=
  LinearMap.toContinuousLinearMap
    { toFun := S.conj ρ d
      map_add' := map_add _
      map_smul' r u := by
        change S.conj ρ d (r • u) = r • S.conj ρ d u
        simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smulₛₗ]; simp }

section Integral
variable {B E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (p : Ortho → B) (hp : Continuous p) (s : Set E)
  (hs : IsOpen s) (f : E × B → F)
  (h : ∀ x∈s, ∀ t, ContDiffAt ℝ ∞ f (x,p t))
include hp h
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private lemma continuous_slice (x : E) (hx : x∈s) :
    Continuous fun i => f (x,p i) := by
  apply continuous_iff_continuousAt.mpr
  intro i
  exact (h x hx i).continuousAt.comp (f:=fun i => (x,p i)) (continuous_const.prodMk hp).continuousAt

private def partialAt (f : E × B → F) (v : E × B) : E →L[ℝ] F :=
  fderiv ℝ (fun x => f (x,v.2)) v.1

omit hp [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private lemma partialAt_diff (x : E) (hx : x∈s) (i : Ortho) : ContDiffAt ℝ ∞ (partialAt f) (x,p i) := by
  exact ContDiffAt.fderiv (f:=fun (v : E×B) (x:E) => f (x,v.2))
    (g:=Prod.fst) (n:=∞)
    ((h x hx i).comp (f:=fun u : (E×B)×E => (u.2,u.1.2)) _
      (by fun_prop)) contDiffAt_fst (by simp)
include hs
private lemma first (x : E) (hx : x∈s) :
    HasFDerivAt (fun y => ∫ a,f (y,p a) ∂angles) (∫ a,partialAt f (x,p a) ∂angles) x := by
  obtain ⟨r,hr,hs'⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx)
  have ht : 0 < r/2 := half_pos hr
  have he : Metric.closedBall x (r/2) ⊆ s := (Metric.closedBall_subset_ball (half_lt_self hr)).trans hs'
  have hb := partialAt_diff p s f h
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x (r/2)).prod (isCompact_range hp)).exists_bound_of_continuousOn
    (f:=partialAt f) (fun q hq => by
      obtain ⟨hy,⟨a,ha⟩⟩ := hq
      exact ((show ContDiffAt ℝ ∞ (partialAt f) q by simpa [ha] using hb q.1 (he hy) a).continuousAt).continuousWithinAt)
  have hy := continuous_slice p hp s f h
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F':=fun y a => partialAt f (y,p a))
    (Metric.closedBall_mem_nhds x ht) ?_
    ((hy x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((continuous_slice p hp s _ hb x hx).aestronglyMeasurable) ?_ (integrable_const C) ?_
  · filter_upwards [hs.mem_nhds hx] with y hy' using (hy y hy').aestronglyMeasurable
  · exact Eventually.of_forall (fun a y hy => hC (y,p a) ⟨hy,a,rfl⟩)
  exact Eventually.of_forall (fun a y hy =>
    ((ContDiffAt.comp (f:=fun v => (v,p a)) y (h y (he hy) a)
      (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by simp)).hasFDerivAt)

/-- Smoothness in external variables integrating O(4) parameter; compactness
at all fixed requests, no uniform in horizon. For a not globally smooth f,
only ask smooth on `{(x,p t) | x ∈ s}`. -/
lemma integral_orbits : ContDiffOn ℝ ∞ (fun y => ∫ a,f (y,p a) ∂angles) s := by
  apply contDiffOn_infty.mpr
  intro k
  induction k generalizing F with
  | zero =>
    have hh : DifferentiableOn ℝ (fun y => ∫ a,f (y,p a) ∂angles) s :=
      fun x hx => (first p hp s hs f h x hx).hasFDerivWithinAt.differentiableWithinAt
    simpa using hh.continuousOn
  | succ k ih =>
    push_cast
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun x hx => (first p hp s hs f h x hx).hasFDerivWithinAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih (partialAt f) (partialAt_diff p s f h)).congr (fun x hx => (first p hp s hs f h x hx).fderiv)
end Integral
end YM.OPE.Cov
