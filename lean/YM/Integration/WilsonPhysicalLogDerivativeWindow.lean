import YM.Integration.WilsonPhysicalTransportWordBound
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! One neighbourhood of the matrix identity and one finite derivative
price for the original group logarithm, before any spatial lattice exists. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalLogDerivativeWindow
open Filter Set Metric Function Finset
open scoped BigOperators ContDiff Topology Matrix.Norms.Frobenius Classical

theorem purchased (G:Gauge) (p:ℕ) :
    ∃δ:ℝ,0<δ ∧ ∃C:ℝ,1≤C ∧ ∀V:G.Mat,‖V-1‖<δ →
      ContDiffAt ℝ ω G.plog V ∧ ∀i≤p,‖iteratedFDeriv ℝ i G.plog V‖≤C :=by
  let C:ℝ:=1+∑i:Fin (p+1),‖iteratedFDeriv ℝ i.val G.plog 1‖
  have ht (i:Fin (p+1)) : ∀ᶠ V:G.Mat in 𝓝 1,
      ‖iteratedFDeriv ℝ i.val G.plog V‖<‖iteratedFDeriv ℝ i.val G.plog 1‖+1:=by
    have h:=G.plog_diff.continuousAt_iteratedFDeriv (k:=i.val) le_top
    exact h.norm.tendsto.eventually (Iio_mem_nhds (lt_add_one _))
  have whole : ∀ᶠ V:G.Mat in 𝓝 1,
      ContDiffAt ℝ ω G.plog V ∧ ∀i≤p,‖iteratedFDeriv ℝ i G.plog V‖≤C:=by
    filter_upwards [G.plog_diff.eventually (by simp), Filter.eventually_all.mpr ht] with V diff each
    refine ⟨diff,fun i hi=>?_⟩
    let j:Fin (p+1):=⟨i,by omega⟩
    have sum:=Finset.single_le_sum (f:=fun u:Fin (p+1)=>‖iteratedFDeriv ℝ u.val G.plog 1‖)
      (fun q _=>norm_nonneg _) (Finset.mem_univ j)
    have one:=each j;change _≤C;unfold C;linarith
  obtain ⟨δ,hδ,sub⟩:=Metric.mem_nhds_iff.mp whole
  refine ⟨δ,hδ,C,?_,fun V hv=>sub (mem_ball.mpr ((dist_eq_norm V 1).trans_lt hv))⟩
  unfold C;have hn:=Finset.sum_nonneg (s:=(Finset.univ:Finset (Fin (p+1))))
    (f:=fun i=>‖iteratedFDeriv ℝ i.val G.plog 1‖) (fun i _=>norm_nonneg _)
  linarith

end YM.Integration.WilsonPhysicalLogDerivativeWindow
