import YM.RG.History
import YM.Extraction.Simultaneous
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
Fixed-period compactness for the *evaluated* normalized vacuum densities of the actual Wilson
history, by smoothing in the output configuration of one true step. This does not identify a
unique subsequential limit or give strong convergence of the label-by-label data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt
open Filter Function Set MeasureTheory Wilson Lattice RG Topology
open scoped BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side}
lemma penaltyZ_continuous (S : StepData c f) : Continuous (fun β : ℝ => S.penaltyZ β G) := by
  rw [continuous_iff_continuousAt]; intro β
  let K := Metric.closedBall β 1 ×ˢ (univ : Set G.El)
  have hc : Continuous (fun x : ℝ × G.El => S.penaltyWeight x.1 x.2) := by unfold StepData.penaltyWeight; fun_prop
  obtain ⟨M,hM⟩ := (((isCompact_closedBall β 1).prod isCompact_univ).image hc.norm).bddAbove
  have ht := tendsto_integral_filter_of_dominated_convergence (μ:=G.probHaar) (l:=𝓝 β)
    (F:=fun z=> S.penaltyWeight z) (fun _ => M)
    (Eventually.of_forall (fun z => (S.penaltyWeight_cont z).aestronglyMeasurable)) (by
      filter_upwards [Metric.closedBall_mem_nhds β (show 0<(1:ℝ) from one_pos)] with x hx
      exact Eventually.of_forall fun v => hM ⟨(x,v),⟨hx,mem_univ _⟩,rfl⟩) (integrable_const M)
    (Eventually.of_forall (fun v => ((hc.comp (continuous_id.prodMk (continuous_const (y:=v)))).continuousAt :
      Tendsto _ _ (𝓝 (S.penaltyWeight β v)))))
  exact ht

lemma noise_continuous_all (S : StepData c f) :
    Continuous fun x : ℝ × (Config G c × Config G c) => S.noise x.1 x.2.1 x.2.2 := by
  unfold StepData.noise StepData.penaltyWeight
  apply continuous_finsetProd; intro b _; apply Continuous.mul
  · exact ((penaltyZ_continuous S).comp continuous_fst).inv₀ (fun x => (StepData.penaltyZ_pos S _).ne')
  fun_prop

lemma density_uniform (S : StepData c f) (hS : S.patch.Branches S.kernel G) {K : Set ℝ} (hK : IsCompact K) :
    (∃ A : ℝ, ∀ β∈K, ∀ U : Config G f, ∀ V, S.density β U V ≤ A) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ β∈K, ∀ U : Config G f, ∀ V W,
      dist V W < δ → |S.density β U V - S.density β U W| ≤ ε) := by
  let φ (x : ℝ × (Config G c × Config G c)) := S.noise x.1 x.2.1 x.2.2
  let P := K ×ˢ (univ : Set (Config G c × Config G c))
  have hP : IsCompact P := hK.prod isCompact_univ
  obtain ⟨M,hM⟩ := (hP.image (noise_continuous_all S)).bddAbove
  refine ⟨⟨M,fun β hβ U V => ?_⟩,fun ε hε => ?_⟩
  · unfold StepData.density
    rw [show M = (∑ t, S.likelihood U t)*M by rw [S.chosen hS,one_mul], Finset.sum_mul]
    exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hM ⟨⟨β,S.prediction U t,V⟩,⟨hβ,mem_univ _⟩,rfl⟩)
      (S.likelihood_pos U t)
  obtain ⟨δ,hδ,hr⟩ := Metric.uniformContinuousOn_iff.mp
    (hP.uniformContinuousOn_of_continuous (f:=φ) (noise_continuous_all S).continuousOn) ε hε
  refine ⟨δ,hδ,fun β hβ U V W hw => ?_⟩; unfold StepData.density; rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  conv_rhs => rw [show ε = (∑ t, S.likelihood U t)*ε by rw [S.chosen hS,one_mul], Finset.sum_mul]
  refine Finset.sum_le_sum fun t _ => ?_; rw [← mul_sub, abs_mul, abs_of_nonneg (S.likelihood_pos U t)]
  let q := S.prediction U t
  refine mul_le_mul_of_nonneg_left (hr (β,q,V) ⟨hβ,mem_univ _⟩ (β,q,W) ⟨hβ,mem_univ _⟩ ?_).le (S.likelihood_pos U t)
  simp only [Prod.dist_eq, max_lt_iff, dist_self, hδ,hw,and_self]

variable {A : History G}
lemma history_eval_nonneg (h : A.Selected) {N m p} (hm : m ≤ N) (V : Config G (A.S.side m p)) :
    0 ≤ (A.rep N p m).eval V := by
  suffices ∀ m, m≤N → ∀ V : Config G (A.S.side m p), 0 ≤ (A.rep N p m).eval V by exact this m hm V
  refine fun m hm => Nat.decreasingInduction (motive:=fun k _ => ∀ V : Config G (A.S.side k p), 0≤(A.rep N p k).eval V) ?_ ?_ hm
  swap
  · rw [(h.starts N p).2]; exact fun V => (bare_pos _ V).le
  intro k hk ih V; rw [(h.steps N p k hk).1]
  exact integral_nonneg fun U => mul_nonneg ((A.levels.transition_mass ..).positive U V) (ih U)

def vacuum (A : History G) (N m p : ℕ) (V : Config G (A.S.side m p)) :=
  (A.rep N p m).eval V / partition G (A.S.side N p) (A.β N p N)

lemma vacuum_integral (h : A.Selected) {N m p} (hm : m ≤ N) : ∫ V, vacuum A N m p V ∂prior G (A.S.side m p) = 1 := by
  unfold vacuum; rw [integral_div,A.partition_eq h _ _ _ hm]; exact div_self (partition_pos ..|>.ne')

lemma vacuum_step (h : A.Selected) {N m p} (hm : m < N) (V : Config G (A.S.side m p)) :
    vacuum A N m p V = ∫ U, ((A.levels.clock.op m p).density (A.β N p (m+1)) U V * vacuum A N (m+1) p U)
      ∂prior G (A.S.side (m+1) p) := by
  unfold vacuum; rw [(h.steps N p m hm).1,StepData.push,← integral_div]
  apply integral_congr_ae; apply Eventually.of_forall; intro U; simp only [smul_eq_mul, mul_div_assoc]

lemma density_input_integrable (h : A.Selected) {N m p} (hm : m < N) (V) : Integrable (fun U =>
    (A.levels.clock.op m p).density (A.β N p (m+1)) U V * vacuum A N (m+1) p U) (prior G (A.S.side (m+1) p)) :=
    StepData.push_slice (S:=A.levels.clock.op m p) (A.levels.transition_mass ..) V _
      (((A.rep N p (m+1)).envelope (h.represents N p (m+1) hm).good).integrable _ |>.div_const _)

private def padded (A : History G) (N m p : ℕ) :=
  if m<N then vacuum A N m p else fun _ => 0

lemma vacuum_compact_bounds (h : A.Selected) (m p : ℕ) :
    (∃ M, ∀ N, ∀ V, padded A N m p V ∈ Icc 0 M) ∧ Equicontinuous (fun N => padded A N m p) := by
  let S := A.levels.clock.op m p
  obtain ⟨⟨M,hM⟩,hh⟩ := density_uniform S (A.levels.blocks m p).branches isCompact_Icc
  have hf {N} (hn : m<N) : Integrable (vacuum A N (m+1) p) (prior G (A.S.side (m+1) p)) := by
    unfold vacuum; exact (((A.rep N p (m+1)).envelope (h.represents N p (m+1) hn).good).integrable _).div_const _
  have hPos N k hK V : 0 ≤ vacuum A N k p V := div_nonneg (history_eval_nonneg h hK V) (partition_pos ..).le
  constructor
  · refine ⟨max M 0,fun N V => ?_⟩; unfold padded; split_ifs with hNm
    swap; exact ⟨le_rfl,le_max_right _ _⟩
    refine ⟨hPos _ _ hNm.le _, (le_max_of_le_left ?_)⟩; rw [vacuum_step h hNm]
    rw [show M = ∫ U, M*vacuum A N (m+1) p U ∂prior G (A.S.side (m+1) p) by rw [integral_const_mul,vacuum_integral h hNm,mul_one]]
    exact integral_mono (density_input_integrable h hNm V) ((hf hNm).const_mul M) (fun U => mul_le_mul_of_nonneg_right
      (hM _ (h.represents N p (m+1) hNm).band U V) (hPos _ _ hNm _))
  intro V; apply Metric.equicontinuousAt_iff.mpr; intro ε hε
  obtain ⟨δ,hδ,hδ'⟩ := hh (ε/2) (half_pos hε)
  refine ⟨δ,hδ,fun x hx N => ?_⟩; unfold padded; split_ifs with hn
  swap; simpa only [dist_self] using hε
  rw [Real.dist_eq, vacuum_step h hn V,vacuum_step h hn x,← integral_sub (density_input_integrable h hn V) (density_input_integrable h hn x)]
  apply lt_of_le_of_lt _ (half_lt_self hε); rw [← Real.norm_eq_abs]; change ‖∫ U,
    (_*vacuum A N (m+1) p U - _*vacuum A N (m+1) p U) ∂prior G (A.S.side (m+1) p)‖ ≤ _
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [show ε/2 = ∫ U, (ε/2)*vacuum A N (m+1) p U ∂prior G (A.S.side (m+1) p) by rw [integral_const_mul,vacuum_integral h hn,mul_one]]
  refine integral_mono (((density_input_integrable h hn V).sub (density_input_integrable h hn x)).norm) ((hf hn).const_mul _) ?_
  intro U; simp only [← sub_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hPos _ _ hn _)]
  exact mul_le_mul_of_nonneg_right (hδ' _ (h.represents N p (m+1) hn).band U V x (dist_comm V x ▸ hx)) (hPos _ _ hn _)

private abbrev BCF (A : History G) (i : ℕ × ℕ) := BoundedContinuousFunction (Config G (A.S.side i.1 i.2)) ℝ

private def bundled (h : A.Selected) (i : ℕ × ℕ) (N : ℕ) : BCF A i :=
  ContinuousMap.equivBoundedOfCompact _ _ ⟨padded A N i.1 i.2,(vacuum_compact_bounds h _ _).2.continuous N⟩

lemma vacuum_subsequence (h : A.Selected) (s : Extraction.Sequence) :
    ∃ g : Extraction.Sequence, ∃ L : ∀ m p, (Config G (A.S.side m p) → ℝ), ∀ m p,
      TendstoUniformly (fun k => vacuum A ((s.after g) k) m p) (L m p) atTop := by
  choose M hm using (fun m p => (vacuum_compact_bounds h m p).1)
  let K (i) := closure (range (bundled h i))
  have hc : ∀ i, IsCompact (K i) := fun ⟨m,p⟩ => BoundedContinuousFunction.arzela_ascoli (Icc 0 (M m p))
    isCompact_Icc _ (fun _ x ⟨k,hk⟩ => hk ▸ hm m p k x) (by
      let u (f : range (bundled h (m,p))) := f.property.choose
      have hu (f : range (bundled h (m,p))) : (fun k => padded A k m p) (u f) = (f.val : Config G (A.S.side m p)→ℝ) := by
        rw [← f.property.choose_spec]; rfl
      change Equicontinuous (fun f : range (bundled h (m,p)) => _)
      rw [show (fun f : range (bundled h (m,p)) => (f.val : Config G (A.S.side m p)→ℝ)) = (fun k => padded A k m p) ∘ u from funext fun f => (hu f).symm]
      exact ((vacuum_compact_bounds h m p).2).comp u)
  obtain ⟨t,y,hy⟩ := Extraction.simultaneous (K:=K) (fun i k => bundled h i (s k)) hc (fun i=> Eventually.of_forall fun k => subset_closure ⟨s k,rfl⟩)
  refine ⟨t,fun m p => y (m,p),fun m p => ?_⟩
  have he := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hy (m,p)).2
  intro B hB
  filter_upwards [he B hB,(s.monotone.tendsto_atTop.comp t.monotone.tendsto_atTop).eventually (eventually_gt_atTop m)] with k hk hkm
  intro q
  have hq := hk q
  change (_, padded A (s (t k)) m p _) ∈ _ at hq
  change m<s (t k) at hkm
  rw [padded,if_pos hkm] at hq
  exact hq
end YM.UVExt
