import YM.OPE.Compatible.Beam

/-!
# The actual C[r] laws

Each group of coefficients of the common representative transforms in the
true rotation representation on the homogeneous subspace. Field labels of
inputs may mix horizons and the output transforms through exactly its own
weight. The vector-valued interpretation avoids basis-specific placement of
indices of rotation matrices; the formula as a finite sum of coefficients
times `axis` is also supplied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov.Display
open Function Set Filter Table Survey Signal MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  {I J : Type} [Fintype I] [Fintype J] (U : Spec.Final C f S)
variable {x : I → E4} (p : I → S.Tag) (o : E4)

/-- Interpretation as the homogeneous output space at weight w. -/
def tint (w : ℕ) (r : ℝ) (x : I → E4) (p : I → S.Tag) (o : E4) : S.Field w :=
  ∑ a : Hue (facets U) w, beam U ⟨w,a⟩ r x p o • (legends U).axis ⟨w,a⟩

lemma tint_as (w : ℕ) (r : ℝ) : tint U w r x p o =
    (ramp (supplies S) w r : ℂ) • (facets U).part w w (ray U w x p o) := by
  unfold tint beam lens; simp_rw [mul_smul]; rw [← Finset.smul_sum]; rw [Catalogue.piece_code]
lemma tint_mem (w : ℕ) (r : ℝ) : tint U w r x p o ∈ (facets U).stratum w := by
  rw [tint_as]; exact Submodule.smul_mem _ _ ((facets U).top_mem _)

private lemma beam_off (a : Tones U) {r : ℝ} (h : 2*period (supplies S) a.fst < r) :
    beam U a r x p o = 0 := by
  rw [beam,off _ _ h,Complex.ofReal_zero,zero_mul]
lemma beam_perm (a : Tones U) {r : ℝ} (h : Covered S r x o) (e : J ≃ I) :
    beam U a r (x ∘ e) (p ∘ e) o = beam U a r x p o := by
  by_cases he : r ≤ 2*period (supplies S) a.fst
  · unfold beam lens ray
    have hf : away (x ∘ e) o = away x o ∘ e := rfl
    rw [hf]
    refine congr_arg _ (congr_arg _ (?_ : ascend _ _ _ _ a.1 _ _ = _))
    exact same_ascend _ _ _ _ _ _ (fun n hn =>
      proj_perm _ U.room.kernel (h.2.2 _ he n hn) p e)
  rw [beam_off U _ _ a (lt_of_not_ge he),beam_off U _ _ a (lt_of_not_ge he)]
lemma beam_shift (a : Tones U) (r : ℝ) (z : E4) :
    beam U a r (fun i => x i+z) p (o+z) = beam U a r x p o := by
  unfold beam lens ray; rw [show away (fun i => x i+z) (o+z) = away x o from funext fun i => by simp [away]]

lemma tint_moves (w : ℕ) {r : ℝ} (h : Covered S r x o) (K : Ortho) :
    U.sector.turns.act w K (tint U w r x p o) = tint U w r (Ortho.move K ∘ x)
      (U.sector.turns.label K ∘ p) (Ortho.move K o) := by
  rw [tint_as, tint_as,map_smul]
  by_cases he : r ≤ 2*period (supplies S) w
  · unfold ray
    rw [rot_part (facets U) (facets_covariant U) U.phase.transport.spots w w le_rfl _ K,
      ascend_rotated (supplies S) U.phase.transport.spots U.room.kernel U.phase.transport.motion (h.2.2 w he),
      show Ortho.move K ∘ away x o = away (Ortho.move K ∘ x) (Ortho.move K o) from
        funext fun i => (Ortho.motion K).map_sub _ _]
  rw [off _ _ (lt_of_not_ge he), Complex.ofReal_zero,zero_smul,zero_smul]

lemma beam_conjugate (r : ℝ) (a : Tones U) :
    beam U a r x (conjugate U.room.kernel.spin ∘ p) o = star (beam U a r x p o) := by
  unfold beam lens ray; rw [← ascend_conjugate _ U.phase.transport.rights, Catalogue.conj_coord _
    U.room.kernel.laws.toSymmetric U.phase.transport.injection U.phase.transport.rights _ _ a
    ((shadows ..).2 le_rfl)]
  simp [star_mul']
lemma beam_unit (z : E4) {r : ℝ} (h : Covered S r (beside (sole z) x) o) (a : Tones U) (n : ℕ) :
    beam U a r (beside (sole z) x) (beside (sole (⟨n,S.unit n⟩:S.Tag)) p) o = beam U a r x p o := by
  by_cases he : r ≤ 2*period (supplies S) a.fst
  · unfold beam lens ray
    have hf : away (beside (sole z) x) o = beside (sole (z-o)) (away x o) := by
      ext1 i; cases i <;> rfl
    have ht := h.2.2 _ he; rw [hf] at ht
    rw [hf]
    apply congr_arg; apply congr_arg
    exact same_ascend _ _ _ _ _ _ (fun j hj =>
      proj_unit _ U.room.kernel (z-o) (ht j hj) p n)
  rw [beam_off U _ _ a (lt_of_not_ge he),beam_off U _ _ a (lt_of_not_ge he)]
lemma beam_straight (n : I → ℕ) {r : ℝ} (h : Covered S r x o) (a : Tones U) :
    ∃ m : MultilinearMap ℂ (fun i => S.Field (n i)) ℂ, ∀ v, beam U a r x (stockTag (d:=n) v) o = m v := by
  by_cases he : r ≤ 2*period (supplies S) a.fst
  · obtain ⟨m,hm⟩ := ascend_straight _ U.phase.transport.spots U.room.kernel (h.2.2 _ he) n
    refine ⟨(ramp (supplies S) a.fst r : ℂ) • ((legends U).readIn a.fst a).compMultilinearMap m,?_⟩
    intro v; unfold beam lens ray; rw [← hm]; rfl
  exact ⟨0,fun v => beam_off U _ _ _ (lt_of_not_ge he)⟩
lemma beam_steps {r : ℝ} {n m : ℕ} (h : Covered S r x o) (a : Tones U) (hn : n ≤ m) (v : S.Field n) (i : I) :
    beam U a r x (update p i ⟨m,U.sector.derivatives.rise hn v⟩) o = beam U a r x (update p i ⟨n,v⟩) o := by
  by_cases he : r ≤ 2*period (supplies S) a.fst
  · unfold beam lens ray
    apply congr_arg; apply congr_arg
    exact ascend_filter (supplies S) U.room.kernel U.phase.transport.injection (h.2.2 _ he) p hn v i
  rw [beam_off U _ _ a (lt_of_not_ge he),beam_off U _ _ a (lt_of_not_ge he)]

lemma beamSmooth {r : ℝ} (h : Covered S r x o) (a : Tones U) :
    ContDiffAt ℝ ∞ (fun y : ℝ × (I → E4) × E4 => beam U a y.1 y.2.1 p y.2.2) (r,x,o) := by
  let D := ℝ × (I → E4) × E4
  by_cases he : r ≤ 2*period (supplies S) a.fst
  · let u := fun y : D => away y.2.1 y.2.2
    have hu : ContDiffAt ℝ ∞ u (r,x,o) := by
      refine contDiffAt_pi.mpr fun i => ContDiffAt.sub ?_ (contDiffAt_snd.comp _ contDiffAt_snd)
      exact contDiffAt_pi.mp (show ContDiffAt ℝ ∞ (fun y : D => y.2.1) (r,x,o) from
        contDiffAt_fst.comp _ contDiffAt_snd) i
    let F := LinearMap.toContinuousLinearMap (((legends U).readIn a.fst a).restrictScalars ℝ)
    refine ContDiffAt.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (f:=(⇑(ramp (supplies S) a.fst) ∘ Prod.fst))
        ((ramp (supplies S) a.fst).contDiff.contDiffAt.comp _ contDiffAt_fst)) (ContDiffAt.comp (g:=F)
        _ F.contDiff.contDiffAt ?_)
    exact (ascend_smooth _ U.phase.transport.spots U.room.kernel (h.2.2 _ he) p).comp (f:=u) _ hu
  apply ContDiffAt.congr_of_eventuallyEq (show ContDiffAt ℝ ∞ (fun _ : D => (0:ℂ)) _ from contDiffAt_const)
  filter_upwards [continuous_fst.continuousAt.tendsto.eventually
    (lt_mem_nhds (lt_of_not_ge he))] with y hy using beam_off U p y.2.2 a hy
end YM.OPE.Cov.Display
