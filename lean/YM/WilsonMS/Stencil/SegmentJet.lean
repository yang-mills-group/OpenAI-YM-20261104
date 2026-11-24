import YM.WilsonMS.Stencil.RadialAt
import YM.Work.G05.Taylor
/-!
# Turning radial gauge into section jets

Full differential on both position and spacing arguments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.RGerm
open Function Filter Set MeasureTheory
open Analysis Tensor Curves TaylorRules TPath Source Paths Work.G05
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {B : Paths.Family G} {a : ℝ} {n k : ℕ}

lemma coeff_ray {f : E → F} (u : E) (h : ContDiffAt ℝ (↑k) f 0) :
    Tensor.diagonal (Tensor.coeff f k 0) u =
      (k.factorial : ℝ)⁻¹ • iteratedDeriv k (fun t : ℝ => f (t • u)) 0 := by
  let L := ContinuousLinearMap.toSpanSingleton ℝ u
  have he := blockTaylor_contDiff k f (↑k)
  have hp : Agree k 0 (blockTaylor k f ∘ L) (f ∘ L) :=
    (Agree.refl (L.contDiff (n := (↑k : WithTop ℕ∞))).contDiffAt).comp
      (by
        rw [map_zero]
        exact ⟨he.contDiffAt, h, blockTaylor_jets h⟩)
  have ht := hp.same k le_rfl
  rw [L.iteratedFDeriv_comp_right he 0 le_rfl, map_zero, blockTaylor_jets h k le_rfl] at ht
  have hu : iteratedFDeriv ℝ k f 0 (fun _ => u) = iteratedDeriv k (f ∘ L) 0 := by
    have hv := DFunLike.congr_fun ht 1
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, L,
      ContinuousLinearMap.toSpanSingleton_apply, Pi.one_apply, one_smul] at hv
    exact hv
  unfold Tensor.diagonal Tensor.coeff
  rw [_root_.smul_apply, hu]
  rfl

abbrev atPulse (i : Axis) (a : ℝ) (B : Paths.Family G) : E4 → G.Color := fun y => pull B i (a, y)

lemma pulseS (h : Flow B) (i : Axis) : ContDiffAt ℝ ∞ (atPulse i a B) 0 :=
  (pull_s h i).comp (f := fun x : E4 => (a, x)) 0 (by fun_prop)

lemma rayH (h : Flow B) (x : E4) (a : ℝ) :
    (fun t : ℝ => ∑ i : Axis, x i • (atPulse i a B (t • x))) =ᶠ[𝓝 0] 0 := by
  let f (t : ℝ) := ∑ i : Axis, x i • atPulse i a B (t • x)
  have he : Tendsto (fun t : ℝ => (a, t • x)) (𝓝 0) (𝓝 (a, 0)) := by
    simpa only [zero_smul] using (show Continuous (fun t : ℝ => (a, t • x)) by fun_prop).tendsto 0
  have hx : ∀ᶠ t : ℝ in 𝓝[≠] 0, f t = 0 := by
    filter_upwards [(he.eventually (root_free h)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht hp
    have hk : t ≠ 0 := hp
    apply smul_right_injective (M := G.Color) hk
    unfold f atPulse
    dsimp only
    rw [Finset.smul_sum, smul_zero]
    simp_rw [smul_smul]
    exact ht
  have hp (i) : ContDiffAt ℝ ∞ (fun t : ℝ => atPulse i a B (t • x)) 0 :=
    (show ContDiffAt ℝ ∞ (atPulse i a B) ((0 : ℝ) • x) from
          by
          rw [zero_smul]
          exact pulseS h _).comp
      (f := fun t => t • x) 0 (by fun_prop)
  have ht : Tendsto f (𝓝 0) (𝓝 (f 0)) :=
    (show ContDiffAt ℝ ∞ f 0 from ContDiffAt.sum fun i _ => (hp i).const_smul _).continuousAt
  have hh : f 0 = 0 :=
    tendsto_nhds_unique (ht.mono_left nhdsWithin_le_nhds)
      (tendsto_congr' hx |>.mpr tendsto_const_nhds)
  change ∀ᶠ t in 𝓝 (0 : ℝ), f t = 0
  filter_upwards [eventually_nhdsWithin_iff.mp hx] with s hs
  by_cases hp : s = 0
  subst s
  exact hh
  exact hs hp

lemma no_constant (h : Flow B) (a : ℝ) (i : Axis) : atPulse i a B 0 = 0 := by
  have hp : ∑ j : Axis, basis i j • (atPulse j a B ((0 : ℝ) • basis i)) = 0 :=
    (rayH h (basis i) a).eq_of_nhds
  simpa using hp

private abbrev rad (j : ℕ) (B : Paths.Family G) (a : ℝ) (i : Axis) :=
  Tensor.coeff (atPulse i a B) (j + 1) 0

lemma radial_from (h : Flow B) : rad n B a ∈ Labels.radial G n := by
  have hv (i) : ContDiffAt ℝ (↑(n + 1 : ℕ)) (atPulse i a B) 0 := contDiffAt_infty.mp (pulseS h i) _
  refine ⟨fun i => Tensor.coeff_symm (hv _), fun x => ?_⟩
  have he (i : Axis) : Tensor.diagonal (rad n B a i) x = _ := coeff_ray x (hv i)
  let f (i : Axis) (t : ℝ) := atPulse i a B (t • x)
  have ht : ∑ i : Axis, x i • iteratedDeriv (n + 1) (f i) 0 = 0 := by
    have hp (i : Axis) : ContDiffAt ℝ (↑(n + 1 : ℕ)) (f i) 0 :=
      (show ContDiffAt ℝ (↑(n + 1 : ℕ)) (atPulse i a B) ((0 : ℝ) • x) from
            by
            rw [zero_smul]
            exact hv _).comp
        (f := fun t => t • x) 0 (by fun_prop)
    have hs (i : Axis) : ContDiffAt ℝ (↑(n + 1 : ℕ)) ((x i) • f i) 0 := (hp i).const_smul (x i)
    have hg := (rayH h x a).iteratedDeriv_eq (n + 1)
    have hi :
      iteratedDeriv (n + 1) (fun t : ℝ => ∑ i : Axis, x i • f i t) 0 =
        ∑ i : Axis, iteratedDeriv (n + 1) ((x i) • f i) 0 :=
      iteratedDeriv_fun_sum (f := fun i : Axis => (x i) • f i) fun i _ => hs i
    change iteratedDeriv (n + 1) (fun t : ℝ => ∑ i : Axis, x i • f i t) 0 = _ at hg
    rw [hi] at hg
    simp_rw [iteratedDeriv_const_smul (hp _)] at hg
    simpa using hg
  simp_rw [he]
  rw [Finset.sum_congr rfl (f := _) (g := fun i =>
      (((n + 1).factorial : ℝ))⁻¹ • x i • iteratedDeriv (n + 1) (f i) 0)
      (fun i hi => smul_comm (x i) _ (iteratedDeriv (n + 1) (f i) 0))]
  rw [← Finset.smul_sum, ht, smul_zero]

def records (h : Flow B) (a : ℝ) : Labels.Jet G := fun n => ⟨rad n B a, radial_from h⟩

lemma block_reads (h : Flow B) (i : Axis) (a : ℝ) (x : E4) :
    Work.G05.blockTaylor n (atPulse i a B) x = Source.potential (n + 1) (records h a) i x := by
  rw [Work.G05.blockTaylor, Finset.sum_apply, Finset.sum_range_succ', potential]
  simp only [Nat.add_sub_cancel]
  rw [show Tensor.diagonal (Tensor.coeff (atPulse i a B) 0 0) x = 0 from
      (Tensor.coeff_apply_zero ..).trans (no_constant h a i),
    add_zero]
  rfl

lemma varies (h : Flow B) (n : ℕ) : ContDiff ℝ ∞ (fun a => records h a n) := by
  let f (a : ℝ) := records h a n
  let L := (Labels.radial G n).subtype
  suffices ht : ContDiff ℝ ∞ (L ∘ f)
    by
    obtain ⟨g, hg⟩ :=
      L.exists_leftInverse_of_injective
        (LinearMap.ker_eq_bot.mpr (show Injective L from Subtype.val_injective))
    change ContDiff ℝ ∞ f
    rw [show f = g.toContinuousLinearMap ∘ (L ∘ f) from funext fun a => Eq.symm ?_]
    exact (show ContDiff ℝ ∞ ⇑(g.toContinuousLinearMap) from ContinuousLinearMap.contDiff _).comp ht
    exact DFunLike.congr_fun hg (f a)
  apply contDiff_pi.mpr
  intro i
  have hs (x : ℝ) : ContDiffAt ℝ ∞ (fun a => rad n B a i) x := by
    let P (p : E4 × ℝ) := pull B i (p.2, p.1)
    have hp : ContDiffAt ℝ ∞ P ((0 : E4), x) :=
      (pull_s (a := x) h i).comp (f := fun p : E4 × ℝ => p.swap) (0, x)
        (show ContDiffAt ℝ ∞ _ _ from contDiffAt_snd.prodMk contDiffAt_fst)
    let W (a : ℝ) := Tensor.coeff P (n + 1) (0, a)
    let v := fun a : Fin (n + 1) => ContinuousLinearMap.inl ℝ E4 ℝ
    let V := ContinuousMultilinearMap.compContinuousLinearMapL (F := G.Color) v
    apply
      ContDiffAt.congr_of_eventuallyEq (f := V ∘ W)
        (V.contDiff.contDiffAt.comp (f := W) _
          ((Tensor.coeff_smooth hp _).comp (f := fun a : ℝ => ((0 : E4), a)) _ (by fun_prop)))
    have hg : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (↑(n + 1 : ℕ)) P (0, y) :=
      (show ContinuousAt (fun y : ℝ => ((0 : E4), y)) x from by fun_prop).tendsto.eventually
        ((contDiffAt_infty.mp hp (n + 1)).eventually (by simp))
    filter_upwards [hg] with y hy
    ext1 s
    exact congr_arg (fun x : G.Color => (((n + 1).factorial : ℝ))⁻¹ • x) (partial_first hy s).symm
  exact contDiff_iff_contDiffAt.mpr hs

lemma potential_s (h : Flow B) (i : Axis) :
    ContDiff ℝ ∞ (fun x : Domain => Source.potential k (records h x.1) i x.2) := by
  unfold potential
  refine ContDiff.sum fun j _ => ?_
  let g : Domain → Labels.Taylor G j := fun x => records h x.1 j
  let S := Labels.axes G j
  let F : Fin (Labels.dim G j) → Domain → G.Color := fun k x => S.repr (g x) k • (S k).value i x.2
  have hp : ContDiff ℝ ∞ g := (varies h j).comp contDiff_fst
  rw [show (fun x : Domain => (records h x.1 j).value i x.2) = _ from ?_]
  refine ContDiff.sum (f := F) (s := Finset.univ) fun k _ => ?_
  · exact
      (show ContDiff ℝ ∞ (fun x => S.repr (g x) k) from
            (show ContDiff ℝ ∞ ⇑((S.coord k).toContinuousLinearMap) from
                  ContinuousLinearMap.contDiff _).comp
              hp).smul
        ((Tensor.diag_smooth _ _).comp (f := Prod.snd) contDiff_snd)
  funext x
  let T := ContinuousMultilinearMap.apply ℝ (fun _ => E4) G.Color (fun _ : Fin (j + 1) => x.2)
  let L : Labels.Taylor G j →ₗ[ℝ] Tensor.T E4 G.Color (j + 1) :=
    (LinearMap.proj i).comp (Labels.radial G j).subtype
  change T (L (g x)) = _
  nth_rw 1 [← S.sum_repr (g x)]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul]
  rfl

lemma precision (h : Flow B) (i : Axis) (a : ℝ) :
    Agree k (a, (0 : E4)) (pull B i)
      (fun x : Domain => Source.potential (k + 1) (records h x.1) i x.2) := by
  let W (x : E4 × ℝ) := pull B i x.swap
  let F (x : E4 × ℝ) := Source.potential (k + 1) (records h x.2) i x.1
  have he : Agree k (0, a) F W := by
    have hc :=
      (potential_s (k := k + 1) h i).comp
        (show ContDiff ℝ ∞ (fun x : E4 × ℝ => x.swap) from
          by
          unfold Prod.swap
          fun_prop)
    refine
      family (contDiffAt_infty.mp (show ContDiffAt ℝ ∞ F (0, a) from hc.contDiffAt) k)
        (contDiffAt_infty.mp
          (show ContDiffAt ℝ ∞ W (0, a) from
            (pull_s h i).comp (f := fun x : E4 × ℝ => x.swap) (0, a)
              (show ContDiffAt ℝ ∞ _ _ from contDiffAt_snd.prodMk contDiffAt_fst))
          k)
        (Eventually.of_forall fun y n hn => ?_)
    have hp := blockTaylor_jets (contDiffAt_infty.mp (pulseS (a := y) h i) k) n hn
    rw [funext (block_reads (n := k) h i y)] at hp
    exact hp
  exact
    (Agree.refl
          (show ContDiffAt ℝ (↑k) (fun p : Domain => p.swap) (a, 0) from
            by
            unfold Prod.swap
            fun_prop)).comp
      (he.symm)
end YM.WilsonMS.RGerm
