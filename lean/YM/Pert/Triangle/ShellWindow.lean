import YM.Pert.Triangle.Cylinder
/-! Existence of a finite open annular test region with uniformly signed Taylor kernel on it. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Function Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
local notation "P" => E4 × E4 × E4
def mask (s : P) : Prop := (s.1∈closedBall 0 18) ∧ s.2.1 ∈ closedBall 0 2 ∧ s.2.2 ∈ Metric.sphere 0 1 ∧ 8 ≤ ‖s.1-s.2.1‖
def finiteBox := {s | mask s}
lemma compactBox : IsCompact finiteBox := IsCompact.of_isClosed_subset (show IsCompact (closedBall (0:E4) 18 ×ˢ closedBall (0:E4) 2 ×ˢ Metric.sphere (0:E4) 1) from (isCompact_closedBall _ _).prod ((isCompact_closedBall ..).prod (isCompact_sphere ..))) (?_) (fun _ h=> ⟨h.1,h.2.1,h.2.2.1⟩)
  where finally
    exact (isClosed_closedBall.preimage continuous_fst).inter ((isClosed_closedBall.preimage (continuous_fst.comp continuous_snd)).inter ((isClosed_sphere.preimage (continuous_snd.comp continuous_snd)).inter (isClosed_le continuous_const (((continuous_fst.comp continuous_id).sub (continuous_fst.comp continuous_snd)).norm))))
def sphereRead (s:P) (r:ℝ) := r^12 * classified s.1 s.2.1 (radial r s.2.2) * stamp
def windowLimit (s : P) := stamp^2 / ‖s.1-s.2.1‖^2
lemma boxPath {S:ℕ→P} {a:P} (hS : Tendsto S atTop (𝓝 a)) (hB : ∀ n,mask (S n))
   {R:ℕ→ℝ} (hR:Tendsto R atTop atTop) : Tendsto (fun n=>sphereRead (S n) (R n)) atTop (𝓝 (windowLimit a)) := by
  unfold sphereRead
  let Z(i:ℕ) := (S i).2.2
  let X(i:ℕ) := (S i).1
  let Y(i:ℕ) := (S i).2.1
  have hz : Tendsto Z atTop (𝓝 a.2.2) := continuous_snd.continuousAt.tendsto.comp (continuous_snd.continuousAt.tendsto.comp hS)
  have hx : Tendsto X atTop (𝓝 a.1) := continuous_fst.continuousAt.tendsto.comp hS
  have hy : Tendsto Y atTop (𝓝 a.2.1) := continuous_fst.continuousAt.tendsto.comp (continuous_snd.continuousAt.tendsto.comp hS)
  have h (k) : ‖Z k‖=1 := by simpa only [sub_zero] using (mem_sphere_iff_norm.mp (hB k).2.2.1)
  have bx k : ‖X k‖ ≤ (100/4 : ℝ) := (by have := mem_closedBall_iff_norm.mp (hB k).1; unfold X; rw [sub_zero] at this; linarith)
  have by' k : ‖Y k‖ ≤ (100/4:ℝ) := (by have := mem_closedBall_iff_norm.mp (hB k).2.1; unfold Y; rw [sub_zero] at this; linarith)
  have gap k : 1 ≤ ‖X k-Y k‖ := (show (1:ℝ)≤8 by norm_num).trans (hB k).2.2.2
  convert! (sphereLimit hR hz h hx hy (show (8:ℝ)<100 by norm_num) bx by' gap).mul_const stamp using 1
  congr 1; unfold windowLimit; ring
lemma window_bounds {s:P} (h:mask s) : 0 < windowLimit s ∧ windowLimit s < |stamp^2| + 1 := by
  unfold windowLimit; have hx := h.2.2.2
  have hy : 1≤‖s.1-s.2.1‖^2 := one_le_pow₀ (by linarith : 1 ≤ ‖s.1-s.2.1‖)
  exact ⟨div_pos (sq_pos_of_ne_zero stamp_ne) (by linarith),(div_le_self (sq_nonneg _) hy).trans_lt (lt_add_of_le_of_pos (le_abs_self _) zero_lt_one)⟩
lemma choose_config : ∃ K:ℝ, ∀ r ≥ K, ∀ s:P, mask s → 0 < sphereRead s r ∧ |sphereRead s r| ≤ |stamp^2|+1 := by
  suffices H:∃ k : ℕ, ∀ r : ℝ, ↑k ≤ r → ∀ s:P, mask s → 0 < sphereRead s r ∧ |sphereRead s r| ≤ |stamp^2|+1 by obtain ⟨k,hk⟩:=H; exact ⟨k,hk⟩
  by_contra! H
  choose! R hR S hS he using H
  have ht : Tendsto R atTop atTop := tendsto_atTop_mono (show ∀ n:ℕ, (n:ℝ) ≤ R n from hR) tendsto_natCast_atTop_atTop
  rcases compactBox.tendsto_subseq (show ∀ n,S n∈finiteBox from hS) with ⟨q,hq,σ,hσ,hT⟩
  obtain ⟨A,B⟩ := window_bounds hq
  have hl := boxPath hT (show ∀ n, mask ((S ∘ σ) n) from fun n=>hS (σ n)) (ht.comp hσ.tendsto_atTop)
  obtain ⟨k,p,u⟩ := ((hl.eventually_const_lt A).and (hl.abs.eventually_lt_const (by rwa [abs_of_pos A] : |windowLimit q| < |stamp^2|+1))).exists
  exact False.elim (not_le_of_gt (he (σ k) p) u.le)
end YM.Pert.Triangle
