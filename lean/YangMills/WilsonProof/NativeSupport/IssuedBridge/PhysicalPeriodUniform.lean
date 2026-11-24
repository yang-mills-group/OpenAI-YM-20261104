import YangMills.WilsonProof.NativeSupport.IssuedBridge.PhysicalPeriodNodes
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedBridge.PhysicalPeriodUniform
open YangMills YangMills.Wilson
open YM.Extraction YM.FullVolume
open Filter Function Set MeasureTheory
open scoped Topology
open IssuedBridge.PhysicalPeriodNodes
variable {g : GaugeGroup} (C : YM.Family g.core)

theorem compact (row : (m n : ℕ) → (Fin n → C.book.Token) → YM.Points n → ℂ)
    (m n : ℕ) (v : Fin n → C.book.Token)
    (cluster : Cluster C .full m n (fun N => lifted C N m v) (row m n v))
    (K : Set (YM.Points n)) (comp : IsCompact K) (inside : K ⊆ periodPatch (wilsonFamily C) m n)
    (ε : ℝ) (pos : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ z ∈ K,
      ∀ x : Fin n → Site ((wilsonFamily C).period m * (wilsonFamily C).denominator N),
      dist (nodePosition (wilsonFamily C) N m x) z < δ →
      dist ((wilsonFamily C).finiteMoment N m v x) (periodValue (appoint C row) m v z) < ε := by
  classical
  simp only [Filter.eventually_atTop]
  by_contra! failed
  choose stage later target owner site close wrong using
    fun k : ℕ => failed (1 / ((k : ℝ) + 1)) (by positivity) k
  obtain ⟨point, member, sub, strict, converges⟩ := comp.isSeqCompact owner
  have cofinal : Tendsto stage atTop atTop := tendsto_atTop_mono later tendsto_id
  have toZero : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have tags : Tendsto (fun j => nodePosition (wilsonFamily C) (stage (sub j)) m (site (sub j))) atTop (𝓝 point) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    have small := (toZero.comp strict.tendsto_atTop).eventually_lt_const (half_pos hδ)
    have picked := (Metric.tendsto_nhds.mp converges) (δ / 2) (half_pos hδ)
    filter_upwards [small,picked] with j near here
    have one : dist (nodePosition (wilsonFamily C) (stage (sub j)) m (site (sub j))) (target (sub j)) < δ / 2 :=
      lt_trans (close (sub j)) near
    calc
      _ ≤ _ := dist_triangle _ (target (sub j)) point
      _ < δ / 2 + δ / 2 := add_lt_add one here
      _ = δ := add_halves δ
  have live := safe C (inside member)
  have raw : Tendsto (fun j => (wilsonFamily C).finiteMoment (stage (sub j)) m v (site (sub j)))
      atTop (𝓝 (row m n v point)) := by
    simp_rw [← moment C]
    exact cluster.2 point live (fun j => representatives C (site (sub j))) (stage ∘ sub)
      (cofinal.comp strict.tendsto_atTop) tags
  have smooth := (cluster.1.continuousAt ((nohitOpen C.S m n).mem_nhds live)).tendsto.comp converges
  have gap : Tendsto (fun j => dist ((wilsonFamily C).finiteMoment (stage (sub j)) m v (site (sub j)))
      (row m n v (target (sub j)))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,dist_self] using raw.dist smooth
  obtain ⟨j,good⟩ := (gap.eventually_lt_const pos).exists
  apply (not_lt_of_ge (wrong (sub j)))
  rwa [appointment C row m n v (inside (owner (sub j)))]

end IssuedBridge.PhysicalPeriodUniform
end
