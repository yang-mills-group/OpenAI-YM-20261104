import YM.Work.G02
/-!
# Compact path parameters

Eventually restrict a partial curve to `I` as a **continuous** function; C^k
near each fibre point suffices for C^k dependence in sup norm. Useful for
transport with path endpoints allowed to vary. All derivatives in this chapter
real.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Curves
open Function Filter Set MeasureTheory Metric
open scoped Topology ContDiff BigOperators Classical
variable {E X F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set X} {p : E} {n : ℕ}
  {f : E × X → F}

def along (S : Set X) (f : E × X → F) (x : E) : C(↥S, F) :=
  if h : Continuous (fun v : S => f (x, v.val)) then ⟨_, h⟩ else 0

lemma path_val (h : ∀ v ∈ S, ContDiffAt ℝ (↑n) f (p, v)) (v : S) : along S f p v = f (p, v.val) := by
  have hc : Continuous (fun v : S => f (p, v.val)) :=
    continuous_iff_continuousAt.mpr fun v =>
      (h _ v.property).continuousAt.comp (f := (fun v : S => (p, v.val)))
        (continuous_const.prodMk continuous_subtype_val).continuousAt
  rw [along, dif_pos hc]
  rfl

section
variable [CompactSpace S]

lemma around (h : ∀ v ∈ S, ContDiffAt ℝ (↑n) f (p, v)) :
    ∀ᶠ y in 𝓝 p, ∀ v ∈ S, ContDiffAt ℝ (↑n) f (y, v) := by
  let U := {u : E × X | ContDiffAt ℝ (↑n) f u}
  have ho : IsOpen U :=
    isOpen_iff_mem_nhds.mpr fun y hy =>
      ContDiffAt.eventually (show ContDiffAt ℝ (↑n) f y from hy) (by simp)
  have hs : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨u, v, hu, _, hU, hv, H⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := p)) hs ho
      (show ({ p } ×ˢ S) ⊆ U from by
        rintro ⟨x, y⟩ ⟨hx, hy⟩
        obtain rfl : x = p := hx
        exact h y hy)
  filter_upwards [hu.mem_nhds (hU (mem_singleton p))] with x hx i hi
  exact H ⟨hx, hv hi⟩

lemma remain_on (h : ∀ v ∈ S, ContDiffAt ℝ (↑n) f (p, v)) :
    ∀ᶠ y in 𝓝 p, ∀ v : S, along S f y v = f (y, v.val) :=
  (around h).mono fun _ hv v => path_val hv v

lemma continuous_frame (h : ∀ v ∈ S, ContDiffAt ℝ (↑n) f (p, v)) : ContDiffAt ℝ 0 (along S f) p := by
  obtain ⟨u, hU, hO, hK⟩ := _root_.mem_nhds_iff.mp (around h)
  apply contDiffAt_zero.mpr
  refine ⟨u, hO.mem_nhds hK, continuousOn_iff_continuous_restrict.mpr ?_⟩
  let V : u × S → E × X := fun x => (x.1.val, x.2.val)
  have hc : Continuous (f ∘ V) :=
    continuous_iff_continuousAt.mpr fun (x, y) =>
      (show ContDiffAt ℝ (↑n) f (x.val, y.val) from hU x.property y.val y.property).continuousAt.comp
        (f := V)
        ((continuous_subtype_val.comp continuous_fst).prodMk
            (continuous_subtype_val.comp continuous_snd)).continuousAt
  let T : C(↥u × ↥S, F) := ⟨f ∘ V, hc⟩
  rw [show (u.restrict (along S f)) = ⇑T.curry from
      funext fun x =>
        ContinuousMap.ext fun y =>
          path_val (show ∀ v ∈ S, ContDiffAt ℝ (↑n) f (x.val, v) from hU x.property) y]
  exact T.curry.continuous

/-- The bounded operation of pointwise contraction of a family of linear
maps with one vector. -/
def contracted (U : C(↥S, E →L[ℝ] F)) : E →L[ℝ] C(↥S, F) := by
  let T : E →ₗ[ℝ] C(↥S, F) :=
    { toFun x := ⟨fun v => U v x, U.continuous.clm_apply continuous_const⟩
      map_add' x y := ContinuousMap.ext fun v => map_add (U v) x y
      map_smul' c x := ContinuousMap.ext fun v => map_smul (U v) c x }
  exact
    T.mkContinuous ‖U‖ fun x =>
      (ContinuousMap.norm_le (T x) (by positivity)).mpr fun v =>
        ((U v).le_opNorm x).trans (mul_le_mul_of_nonneg_right (U.norm_coe_le_norm v) (norm_nonneg x))

omit [NormedSpace ℝ X] in
lemma contracting (U : C(↥S, E →L[ℝ] F)) (x : E) (v : S) : contracted U x v = U v x :=
  rfl

def contractL (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] : C(↥S, E →L[ℝ] F) →L[ℝ] (E →L[ℝ] C(↥S, F)) := by
  let T : C(↥S, E →L[ℝ] F) →ₗ[ℝ] (E →L[ℝ] C(↥S, F)) :=
    { toFun := contracted
      map_add' U W := by
        ext x v
        rfl
      map_smul' r U := by
        ext x v
        rfl }
  refine
    LinearMap.mkContinuous (σ := RingHom.id ℝ) (E := C(↥S, E →L[ℝ] F)) (F := E →L[ℝ] C(↥S, F)) T 1
      fun U => ?_
  rw [one_mul]
  exact
    (T U).opNorm_le_bound (norm_nonneg U) fun x =>
      (ContinuousMap.norm_le _ (by positivity)).mpr fun v =>
        ((U v).le_opNorm x).trans (mul_le_mul_of_nonneg_right (U.norm_coe_le_norm v) (norm_nonneg x))

private def pre (f : E × X → F) (x : E × X) : E →L[ℝ] F :=
  (fderiv ℝ f x).comp (ContinuousLinearMap.inl ℝ E X)

private lemma cont_pre {v : E × X} (h : ContDiffAt ℝ (↑(n + 1 : ℕ)) f v) :
    ContDiffAt ℝ (↑n) (pre f) v := by
  exact
    (h.fderiv_right
          (by
            push_cast
            rfl)).clm_comp
      contDiffAt_const

private lemma key {v : X} (h : ContDiffAt ℝ (↑(n + 1 : ℕ)) f (p, v)) :
    HasFDerivAt (fun x : E => f (x, v)) (pre f (p, v)) p :=
  ((h.differentiableAt
        (by
          push_cast
          simp)).hasFDerivAt.comp
    (f := fun x : E => (x, v)) p ((hasFDerivAt_id p).prodMk (hasFDerivAt_const v p)))

private lemma globalDiff (h : ∀ v ∈ S, ContDiffAt ℝ (↑(n + 1 : ℕ)) f (p, v)) :
    HasFDerivAt (along S f) (contracted (along S (pre f) p)) p := by
  let U := along S (pre f)
  let q := around h
  have hc := (continuous_frame (fun v (hv : v ∈ S) => cont_pre (h v hv))).continuousAt
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε he
  obtain ⟨r, hr, hB⟩ :=
    Metric.mem_nhds_iff.mp (q.and (hc.tendsto.eventually (ball_mem_nhds (U p) he)))
  let B := ball p r
  have hb (x : E) (hx : x ∈ B) : ∀ v ∈ S, ContDiffAt ℝ (↑(n + 1 : ℕ)) f (x, v) := (hB hx).1
  filter_upwards [ball_mem_nhds p hr] with x hx
  apply (ContinuousMap.norm_le _ (mul_nonneg he.le (norm_nonneg (x - p)))).mpr
  intro v
  change ‖along S f x v - along S f p v - along S (pre f) p v (x - p)‖ ≤ _
  rw [path_val (hb x hx), path_val h, path_val (n := n) (fun i hi => cont_pre (h i hi))]
  refine
    (convex_ball p r).norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fun x : E => f (x, v.val))
      (φ := pre f (p, v.val)) (fun x hx => (key (hb x hx _ v.property)).hasFDerivWithinAt) ?_
      (mem_ball_self hr) hx
  intro y hy
  rw [← path_val (n := n) (p := y) (fun i hi => cont_pre (hb y hy i hi)) v, ←
    path_val (n := n) (fun i hi => cont_pre (h i hi)) v]
  apply le_of_lt
  apply lt_of_le_of_lt ((U y - U p).norm_coe_le_norm v)
  rw [← dist_eq_norm]
  exact (hB hy).2

theorem contDiff_along (h : ∀ v ∈ S, ContDiffAt ℝ (↑n) f (p, v)) : ContDiffAt ℝ (↑n) (along S f) p := by
  induction n generalizing F with
  | zero => exact continuous_frame h
  | succ n ih =>
    push_cast
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨_, ⟨_, around h, fun x hx => globalDiff (n := n) (p := x) (f := f) hx⟩, ?_⟩
    exact
      (contractL (S := S) E F).contDiff.contDiffAt.comp (f := along S (pre f)) p
        (ih (fun i hi => cont_pre (h i hi)))
end
end YM.WilsonMS.Curves
