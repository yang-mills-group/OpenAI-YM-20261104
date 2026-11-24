import YM.Integration.WilsonPhysicalLogDerivativeWindow

/-! Block-length-independent chain estimate for the fixed physical group
logarithm along a one-dimensional interpolation of a real holonomy. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalLogChainPrice
open Set Function Finset Metric
open scoped BigOperators ContDiff Topology Matrix.Norms.Frobenius Classical

theorem sum {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p j:ℕ} (hj:j≤p) (g:E→F) (f:ℝ→E) (t:ℝ) (hg:ContDiffAt ℝ p g (f t)) (hf:ContDiffAt ℝ p f t)
    {C B:ℝ} (c0:0≤C) (b1:1≤B)
    (out:∀i≤p,‖iteratedFDeriv ℝ i g (f t)‖≤C) (inside:∀i≤p,‖iteratedDeriv i f t‖≤B) :
    ‖iteratedDeriv j (g ∘ f) t‖≤(Fintype.card (OrderedFinpartition j):ℝ)*(C*B^p) :=by
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hg hf (by exact_mod_cast hj)]
  refine (norm_sum_le ..).trans ?_
  calc
    _ ≤ ∑ _k:OrderedFinpartition j,C*B^p:=by
      apply Finset.sum_le_sum;intro u _
      refine ((iteratedFDeriv ℝ u.length g (f t)).le_opNorm _).trans ?_
      have prod : (∏ k:Fin u.length,‖iteratedDeriv (u.partSize k) f t‖)≤B^u.length:=by
        have bound:=Finset.prod_le_prod (s:=(Finset.univ:Finset (Fin u.length)))
          (f:=fun k=>‖iteratedDeriv (u.partSize k) f t‖) (g:=fun _=>B)
          (fun k _=>norm_nonneg _) (fun k _=>inside _ ((u.partSize_le k).trans hj))
        simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using bound
      exact mul_le_mul (out _ (u.length_le.trans hj)) (prod.trans (pow_le_pow_right₀ b1 (u.length_le.trans hj)))
        (Finset.prod_nonneg (fun _ _=>norm_nonneg _)) c0
    _ = _ := by simp

theorem purchased (G:Gauge) (p:ℕ) : ∃δ:ℝ,0<δ ∧ ∃C:ℝ,1≤C ∧
    ∀(f:ℝ→G.Mat) (t B:ℝ),‖f t-1‖<δ → ContDiffAt ℝ p f t → 1≤B →
    (∀i≤p,‖iteratedDeriv i f t‖≤B) → ∀j≤p,
    ‖iteratedDeriv j (G.plog ∘ f) t‖≤(Fintype.card (OrderedFinpartition j):ℝ)*(C*B^p):=by
  obtain ⟨δ,pos,C,c1,price⟩:=WilsonPhysicalLogDerivativeWindow.purchased G p
  refine ⟨δ,pos,C,c1,fun f t B near hf b1 bounds j hj=>?_⟩
  obtain ⟨hot,charge⟩:=price _ near
  exact sum hj G.plog f t (hot.of_le le_top) hf (zero_le_one.trans c1) b1 charge bounds

end YM.Integration.WilsonPhysicalLogChainPrice
