import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Orin
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Suites

/-!
# Physical gauge averaging after the auxiliary directional-jet step

 Build an evaluator that uses the LINK charts of all orders requested. Extension
 is for the real reconstructed function, not an analytic extension of a mask.
 Keep one tube in gauge parameters so no germ shrinking costs later in the
 comparison. `live` is global smooth+jet fee on the whole compact group;
 `rightC` only claimed in its band. If a group-varying q, etc: no uniformity
 over G here, can buy it once before construction choices on each G.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Ward
open Function Filter MeasureTheory RG
open ConnectedActivityE6 Blaze Brush
open scoped Matrix.Norms.Frobenius Topology ContDiff InnerProductSpace Classical BigOperators
attribute [local instance] Gauge.frobInner
structure Visage (G:Gauge)(k:ℕ) where
  logG : G.Mat → G.Color
  cost : ℝ
  radius : ℝ
  pricey : 0 < cost
  charged : 0 < radius
  on_one : logG 1=0
  bloom : ContDiff ℝ (k:WithTop ℕ∞) logG
  rightC (u:G.El): ‖G.mat u-1‖ ≤ radius → G.lieExp (logG (G.mat u))=u
  live (u:G.El) : Brush k cost 1 logG (G.mat u)
variable (G:Gauge)(k:ℕ)
-- chart inverse is in El topology; use subembedding
lemma vista (G:Gauge)(k:ℕ): Nonempty (Visage G k):= by
  have hb := (Continuous.isClosedEmbedding (f:=G.mat) G.continuous_mat G.mat_injective).isEmbedding
  have hh:= G.plog_right
  rw [hb.isInducing.nhds_eq_comap 1] at hh
  obtain ⟨s,hs,hx⟩:= ((Metric.nhds_basis_closedBall.comap G.mat).mem_iff).mp  hh
  let K : WithTop ℕ∞:=k
  obtain ⟨r,hr,h⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (show ∀ᶠ x:G.Mat in 𝓝 1, ContDiffAt ℝ K G.plog x from ((G.plog_diff.of_le (show (↑k:WithTop ℕ∞) ≤ _ from le_top)).eventually (by simp)))
  let η : ContDiffBump (1:G.Mat):= ⟨r/2,r,half_pos hr,half_lt_self hr⟩
  let f x:= η x • G.plog x
  have hl X (hX: X∈ Metric.closedBall 1 (r/2)) : f X=G.plog X:= by unfold f; rw [η.one_of_mem_closedBall hX,one_smul]
  have he : ContDiff ℝ K f:=contDiff_iff_contDiffAt.mpr (fun x=> by
    by_cases hv:x∈Metric.closedBall 1 r
    · exact (η.contDiff (n:= (↑k:ℕ∞))
        ).contDiffAt.smul (show ContDiffAt ℝ K G.plog x from h hv)
    refine (show ContDiffAt ℝ K (fun _ : G.Mat=> (0:G.Color)) x from contDiffAt_const).congr_of_eventuallyEq ?_
    filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hv] with x hx'
    unfold f; rw [show η x=0 from notMem_support.mp ?_,zero_smul]
    rw [ContDiffBump.support_eq]; intro he'; exact hx' (Metric.ball_subset_closedBall he'))
  have hh : IsCompact (Set.range G.mat):= isCompact_range G.continuous_mat
  obtain ⟨v,hv,hk⟩:= Brush.compact hh (fun i _=> (show ContDiffAt ℝ (↑k:WithTop ℕ∞) f i from he.contDiffAt))
  refine ⟨f,v,min s (r/2),hv,lt_min hs (half_pos hr),by rw [hl _ (Metric.mem_closedBall_self (half_pos hr).le),G.plog_one],he,?_,fun u=> hk _ ⟨_,rfl⟩⟩
  intro u hp
  rw [hl _ (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hp.trans (min_le_right ..)))]
  exact hx (show G.mat u ∈ Metric.closedBall (G.mat 1) s from Metric.mem_closedBall.mpr (by rw [dist_eq_norm,G.mat_one]; exact hp.trans (min_le_left ..)))

end YM.RGComparison01.Ward
