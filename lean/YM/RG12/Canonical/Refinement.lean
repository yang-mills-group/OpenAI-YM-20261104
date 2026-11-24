import YM.RG12.Canonical.Charts

/-!
# Exact physical meaning of the limits of the columns

Extract on one filter, simultaneously at all k,d. Implements the outlet meaning even for
representatives only observed on arbitrary further sublimits of it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12
open Function Filter Lattice RG Source
open scoped Topology BigOperators

variable {G : Gauge} (C : Family G) (hC : C.Makes)

theorem ultrafilter_converges {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {I : Type*} (u : Ultrafilter I) (f : I → E) (a : ℝ)
    (h : ∀ᶠ i in (u : Filter I), ‖f i‖ ≤ a) :
    ∃ x : E, Tendsto f (u : Filter I) (𝓝 x) := by
  obtain ⟨x, -, hx⟩ := (isCompact_closedBall (0:E) a).ultrafilter_le_nhds' (u.map f) (by
    rw [Ultrafilter.mem_map]; exact h.mono fun i hi => Metric.mem_closedBall.mpr (by rwa [dist_zero_right]))
  exact ⟨x,(show Tendsto f (u : Filter I) (𝓝 x) by rwa [Ultrafilter.coe_map] at hx)⟩

/-- All `d` and `k` passing to the limit on the *same* filter; not a successive limit. -/
structure Observing (φ : Filter UVIndex) (M : ∀ d : ℕ, ℕ → RepChart C d) : Prop where
  grows : Tendsto Prod.fst φ atTop
  tends d k (h₁ : C.ref d ≤ k) : Tendsto (atK C hC d k) φ (𝓝 (M d k))

theorem observe_all {φ : Filter UVIndex} [φ.NeBot]
    (h : Tendsto Prod.fst φ atTop) :
    ∃ (l : Filter UVIndex), l.NeBot ∧ l ≤ φ ∧
      ∃ M : ∀ d : ℕ, ℕ → RepChart C d, Observing C hC l M := by
  let u := Ultrafilter.of φ
  have hu : ↑u ≤ φ := Ultrafilter.of_le φ
  refine ⟨u,inferInstance,hu,?_⟩
  have hx (d k) : ∃ f : RepChart C d, C.ref d ≤ k → Tendsto (atK C hC d k) (u:Filter UVIndex) (𝓝 f) := by
    by_cases hk : C.ref d ≤ k
    · obtain ⟨a, ha⟩ := atK_fixed_budget C hC d k hk
      obtain ⟨f, hf⟩ := ultrafilter_converges u (atK C hC d k) a (((h.mono_left hu).eventually_ge_atTop k).mono fun i hi => ha i hi)
      exact ⟨f, fun _ => hf⟩
    exact ⟨0, fun e => False.elim (hk e)⟩
  choose f hf using hx
  exact ⟨f,h.mono_left hu,hf⟩

variable {C hC} {φ : Filter UVIndex} {M : ∀ d : ℕ, ℕ → RepChart C d}
variable (h : Observing C hC φ M)

include h
lemma Observing.columns (d k : ℕ) (h₁ : C.ref d ≤ k) (v : C.label d)
    {l : Filter UVIndex} (he : l ≤ φ) :
    Tendsto (fun i => atK C hC d k i v) l (𝓝 (M d k v)) :=
  ((Continuous.clm_apply
    (continuous_id : Continuous (id : RepChart C d → RepChart C d))
    (continuous_const (y:=v))).continuousAt.tendsto.comp ((h.tends d k h₁).mono_left he))

theorem Observing.purchase (d k : ℕ) (h₁ : C.ref d ≤ k) {l : Filter UVIndex} (he : l ≤ φ)
    (v : C.label d) :
    ∃ q : UVIndex → C.label d, Tendsto q l (𝓝 (M d k v)) ∧
      ∀ᶠ i in l, Next.UVStress.quota C d k i.1 i.2 (q i) ≤ mass C d v :=
  ⟨fun i => atK C hC d k i v, h.columns d k h₁ v he,
    ((h.grows.mono_left he).eventually_ge_atTop k).mono fun i hi => (quota_atK C hC _ _ i h₁ hi v).le⟩

theorem Observing.value (d k : ℕ) (h₁ : C.ref d ≤ k) {l : Filter UVIndex} [l.NeBot]
    (he : l ≤ φ) (q : UVIndex → C.label d) (x : C.label d) (z : ℝ)
    (hB : ∀ᶠ i in l, Next.UVStress.quota C d k i.1 i.2 (q i) ≤ z)
    (hx : Tendsto q l (𝓝 x)) :
    ∃ v : C.label d, x = M d k v ∧ mass C d v ≤ z := by
  let f (i : UVIndex) := charts C hC d k i (q i)
  have hg : ∀ᶠ i : UVIndex in l, k ≤ i.1 := (h.grows.mono_left he).eventually_ge_atTop _
  have hf : ∀ᶠ i in l, mass C d (f i) ≤ z := by
    filter_upwards [hB,hg] with i hB hg using (quota_charts C hC _ _ i h₁ hg _).symm.le.trans hB
  obtain ⟨l',hl,H,v,hv⟩ := Next.UVStress.finite_extract f z (hf.mono fun i hi => (norm_le_mass ..).trans hi)
  let j (x : RepChart C d × C.label d) := x.1 x.2
  have hy : Tendsto (fun i => j (atK C hC d k i, f i)) l' (𝓝 (j (M d k,v))) :=
    ((continuous_fst.clm_apply continuous_snd : Continuous j).continuousAt.tendsto.comp
      (((h.tends d k h₁).mono_left (hl.trans he)).prodMk_nhds hv))
  exact ⟨v,tendsto_nhds_unique (hx.mono_left hl)
    (hy.congr fun i => show (charts C hC d k i).symm (charts C hC d k i (q i)) = q i from
      LinearEquiv.symm_apply_apply ..),
    le_of_tendsto ((continuous_mass C d).continuousAt.tendsto.comp hv) (hf.filter_mono hl)⟩

theorem Observing.characterize (S : Table C.book) (d k : ℕ) (h₁ : C.ref d ≤ k)
    {l : Filter UVIndex} [l.NeBot] (he : l ≤ φ) (x : S.Field d) (z : ℝ) :
    (∃ (y : C.label d) (q : UVIndex → C.label d),
      S.project d y = x ∧ Tendsto q l (𝓝 y) ∧
      ∀ᶠ i in l, Next.UVStress.quota C d k i.1 i.2 (q i) ≤ z) ↔
    ∃ v : C.label d, S.project d (M d k v) = x ∧ mass C d v ≤ z := by
  refine ⟨?_,?_⟩
  · rintro ⟨y,q,hy,hq,hB⟩
    obtain ⟨v,rfl,hv⟩ := h.value d k h₁ he q y z hB hq
    exact ⟨v,hy,hv⟩
  rintro ⟨v,hv,hB⟩
  obtain ⟨q,hq,he⟩ := h.purchase d k h₁ he v
  exact ⟨_,q,hv,hq,he.mono fun _ hi => hi.trans hB⟩

end YM.RG12
