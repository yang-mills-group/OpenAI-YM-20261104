import YM.OPE.Compatible.Trees.Layout

/-!
# Turning sequences of layouts into a finite rate experiment

Negative log of the root length plus sum of log gaps of *all* collapsing
edges. Pass to a regime where vertex rates exist; no admission demand going
to infinity along that regime. This sums exactly the ε costs in the budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type} [PartialOrder V] [OrderBot V] [Fintype V] (E:Origin V)

def jump (t:V→ ℝ) (v:V) := t v-t (par E v)
def rat (s:V→ℝ)(v:V) := s v / s (par E v)
def length (t:V→ℝ):ℝ := t ⊥ + ∑ v∈ rest (heart V), jump E t v

def trail (P:Finset V) (v:V) := (rest P).filter fun i => i ≤ v
omit [Fintype V] in
lemma trail_nil (P:Finset V) : trail P ⊥=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun _ h =>
  (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 (le_bot_iff.mp (Finset.mem_filter.mp h).2))
lemma trail_par (P:Finset V){v:V} (hv : v∈rest P) :
    trail P v=insert v (trail P (par E v)) ∧ v∉trail P (par E v) := by
  have hp := from_par E (Finset.mem_erase.mp hv).1
  refine ⟨Finset.ext fun i => ?_,fun e => hp.not_ge (Finset.mem_filter.mp e).2⟩
  rw [Finset.mem_insert]; constructor
  · intro h; obtain ⟨hi,hw⟩ := Finset.mem_filter.mp h; rcases hw.lt_or_eq with h|h
    exact Or.inr (Finset.mem_filter.mpr ⟨hi,touch_par E h⟩)
    exact Or.inl h
  rintro (rfl|h)
  · exact Finset.mem_filter.mpr ⟨hv,le_rfl⟩
  obtain ⟨hi,hq⟩ := Finset.mem_filter.mp h; exact Finset.mem_filter.mpr ⟨hi,hq.trans hp.le⟩
lemma path_sum {P:Finset V}(hP:Crown P) (v:V) (hv:v∈P) (t:V→ℝ) :
    t ⊥+(∑ i∈ trail P v, jump E t i)=t v := by
  revert hv; apply journey E (P:=fun v:V => v∈P → t ⊥+(∑ i∈ trail P v,jump E t i)=t v)
  · simp [trail_nil]
  intro i hi ih hv; obtain ⟨e,he⟩ := trail_par E P ((rest_mem _).mpr ⟨hi,hv⟩)
  rw [e,Finset.sum_insert he,jump]; linarith only [ih (hP.roots (par_le ..) hv)]

variable {M η : ℝ} {s:V→ℝ} {x:V→ E4}
lemma run_climbs (H:Layout E M η s x) {v w:V} (hv:v∈heart V) (h:w ≤ v) : run (s w) ≤ run (s v) :=
  neg_le_neg (Real.log_le_log (H.pos v hv) (H.earlier E hv h))
lemma run_jump (H:Layout E M η s x) {v:V} (h:v∈rest (heart V)) : 0 ≤ jump E (run ∘ s) v :=
  sub_nonneg.mpr (run_climbs E H (Finset.mem_erase.mp h).2 (par_le ..))
lemma run_span (H:Layout E M η s x) (v:V) (hv:v∈heart V) : run (s v) ≤ length E (run ∘ s) := by
  change (run ∘ s) v ≤ (run ∘ s) ⊥ + _
  -- no rewrite in jump
  refine le_trans (path_sum E (tall (internal_le hv bot_le)) v hv (run ∘ s)).ge ?_
  exact add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
    (fun i hi _ => run_jump E H hi))

variable {l : Type} {φ : Filter l} {T:l→ ℝ} {t:V→ ℝ} {S:l→ V→ ℝ} {X:l→ V→ E4}

/-- Need the global geometry even on unary paths. Rates t on internal lengths. -/
structure Layer (φ : Filter l) (T:l→ℝ) (M η:ℝ) (t:V→ℝ) (S:l→V→ℝ) (X:l→V→ E4) : Prop where
  canopy : ⊥∈ heart V
  extent : 0 ≤ M
  space : 0 < η
  flow : Tendsto T φ atTop
  stays : ∀ᶠ i in φ, Layout E M η (S i) (X i)
  reach : Tendsto (fun i=> S i ⊥) φ (𝓝[>] 0)
  prices v : v∈heart V → RateIs φ T (fun i => S i v) (- t v)
  bounds v : v∈heart V → t v∈ Icc (0:ℝ) 1
  charged : length E t=1
lemma refinement [φ.NeBot] (h : ⊥∈ heart V) (hM : 0≤ M) (hη : 0<η)
    (hp : ∀ᶠ i in φ, Layout E M η (S i) (X i)) (hr : Tendsto (fun i=>S i ⊥) φ (𝓝[>] 0)) :
    ∃ ψ : Filter l, ψ.NeBot ∧ ψ ≤ φ ∧ ∃ (T:l→ℝ) (t:V→ℝ), Layer E ψ T M η t S X := by
  let T := fun i => length E (run ∘ S i)
  have hh := run_towards hr
  have hT : Tendsto T φ atTop := tendsto_atTop.mpr (fun a => (((hh.eventually_ge_atTop a).and hp).mono
    fun i e => le_trans e.1 (run_span E e.2 _ h)))
  let z (i:l) (v:V) := if v∈heart V then run (S i v)/T i else 0
  let I := Set.pi univ (fun _ : V => Set.Icc (0:ℝ) 1)
  have hz : IsCompact I := isCompact_univ_pi fun _ => isCompact_Icc
  have he : ∀ᶠ i in φ,z i ∈ I := by
    filter_upwards [hp,hT.eventually_gt_atTop 0, hh.eventually_ge_atTop 0] with i hi hg hh v _
    unfold z; split_ifs with hV
    · exact ⟨div_nonneg (le_trans hh (run_climbs E hi hV bot_le)) hg.le,
        (div_le_one hg).mpr (run_span E hi v hV)⟩
    exact ⟨le_rfl,zero_le_one⟩
  obtain ⟨t,ht,hzt⟩ := hz.exists_mapClusterPt_of_frequently he.frequently
  let ψ := Filter.comap z (𝓝 t) ⊓ φ
  haveI hQ : ψ.NeBot := neBot_inf_comap_iff_map'.mpr hzt
  have hw : ψ ≤ φ := inf_le_right
  have hg : Tendsto z ψ (𝓝 t) := tendsto_comap.mono_left inf_le_left
  have hv (v:V) (h:v∈heart V) : Tendsto (fun i=>run (S i v)/T i) ψ (𝓝 (t v)) := by
    apply (tendsto_pi_nhds.mp hg v).congr (fun i => if_pos h)
  refine ⟨ψ,hQ,hw,T,t,h,hM,hη,hT.mono_left hw,hp.filter_mono hw,hr.mono_left hw,fun v h =>
    ⟨(hp.filter_mono hw).mono (fun i hi=>hi.pos v h),?_⟩,fun v _ => ht v (mem_univ v),?_⟩
  · apply (hv v h).neg.congr
    intro i; simp [run,neg_div]
  have hs v (hv:v∈rest (heart V)) := ((Finset.mem_erase.mp hv).2)
  have ha := (hv ⊥ h).add (tendsto_finsetSum (rest (heart V)) fun v g =>
    (hv v (hs v g)).sub (hv (par E v) (internal_le (hs v g) (par_le ..))))
  unfold length
  refine tendsto_nhds_unique ha (tendsto_const_nhds.congr' ?_)
  filter_upwards [hT.eventually_gt_atTop 0|>.filter_mono hw] with i hi
  simp_rw [← sub_div,← Finset.sum_div,← add_div]
  exact (div_self hi.ne').symm

variable (L : Layer E φ T M η t S X)
include L
lemma Layer.order [φ.NeBot] {v w:V} (hv : v∈heart V) (h : w ≤ v) : t w ≤ t v :=
  neg_le_neg_iff.mp (le_of_tendsto_of_tendsto (L.prices _ hv).rate
    (L.prices _ (internal_le hv h)).rate (((L.flow.eventually_ge_atTop 0).and L.stays).mono (fun _ hi =>
      div_le_div_of_nonneg_right (Real.log_le_log (hi.2.pos v hv) (hi.2.earlier E hv h)) hi.1)))
lemma Layer.fade (v:V) (hv:v∈heart V) : Tendsto (fun i=> S i v) φ (𝓝[>] 0) := by
  have hp := (L.prices v hv).pos
  exact tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero' (hp.mono fun _ => le_of_lt)
    (L.stays.mono (fun i hi=>hi.earlier E hv bot_le)) (L.reach.mono_right nhdsWithin_le_nhds),hp⟩
lemma Layer.jump_rate {v:V} (hv:v∈rest (heart V)) : RateIs φ T (fun i => rat E (S i) v) (-jump E t v) := by
  have h := (Finset.mem_erase.mp hv).2
  apply ((L.prices v h).div (L.prices _ (internal_le h (par_le ..)))).swap
  dsimp [jump]; ring
end YM.OPE.Arboreal
