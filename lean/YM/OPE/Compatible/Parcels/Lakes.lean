import YM.OPE.Compatible.Parcels.Road
/-! Limits of kernel budgets, differences. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG
open scoped Topology Classical BigOperators
variable {I J K:Type*}
variable {X:Type*}[NormedAddCommGroup X]
namespace Sack
variable {p q:I→X} {A B L:ℝ} {u v:I→ℝ}
lemma upto (h:Sack u p A)(x:Finset I): ∑ i∈x, u i*‖p i‖≤A:=(h.2.1.sum_le_tsum x (fun i _=> h.1 i)).trans h.2.2
lemma made (h:∀ x:Finset I, ∑ i∈x,u i*‖p i‖ ≤ A)(ha:0 ≤ u): Sack u p A:=by
    let t i:= u i*‖p i‖; have hp : 0 ≤ t:= fun i=> mul_nonneg (ha i) (norm_nonneg _); have hh:=summable_of_sum_le hp h; exact ⟨hp,hh,hh.tsum_le_of_sum_le h⟩
lemma closes {f:J→I→X} {l:Filter J}[l.NeBot] {a:J→ℝ}(hx:∀ᶠ i in l,Sack u (f i) (a i))(ht:Tendsto a l (𝓝 A))(hp:∀ i,Tendsto (fun j=>f j i) l (𝓝 (p i)))(hu:0≤ u): Sack u p A:=by
    apply made _ hu; intro k; exact le_of_tendsto_of_tendsto (tendsto_finsetSum _ fun i _=> ((hp i).norm).const_mul (u i)) ht (hx.mono fun j hj=> (hj.upto k))
lemma reaches {l:Filter J} {f:J→ I→X}{a:J→ℝ}(hp:∀ᶠ i in l,Sack u (f i-p) (a i))(h:Tendsto a l (𝓝 0))(hu:1 ≤ u)(i:I): Tendsto (fun j=> f j i) l (𝓝 (p i)):=by
   refine (tendsto_sub_nhds_zero_iff.mp ?_); refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) ?_ h)
   filter_upwards [hp] with j hj; exact (le_mul_of_one_le_left (norm_nonneg _) (hu i)).trans (hj.single i)
lemma finalSeq [CompleteSpace X]{f:ℕ→ I→X}{a:ℕ→ℝ}(h:∀ i j,i≤ j→ Sack u (f i-f j) (a i))(hc:Tendsto a atTop (𝓝 0))(hu:1 ≤ u):∃ p:I→X,(∀ i,Tendsto (fun j=> f j i) atTop (𝓝 (p i)))∧∀ i,Sack u (f i-p) (a i):=by
   have hv (i:I): CauchySeq fun j=> f j i:=by
      apply Metric.cauchySeq_iff.mpr; intro ε he
      obtain ⟨N,hN⟩:= eventually_atTop.mp (hc.eventually (gt_mem_nhds he)); have h (j:ℕ)(k:ℕ)(hk:N≤ j)(ht:j ≤ k):dist (f j i) (f k i)< ε := by
         rw [dist_eq_norm]; exact ((le_mul_of_one_le_left (norm_nonneg _) (hu i)).trans ((h j k ht).single i)).trans_lt (hN _ hk)
      refine ⟨N,fun j hj k hk=>?_⟩; rcases le_total j k with r|r; exact h j k hj r
      rw [dist_comm]; exact h k j hk r
   choose Q hp using fun i=> cauchySeq_tendsto_of_complete (hv i)
   exact ⟨Q,hp,fun i=> closes (a:=fun _=>a i) (f:=fun j=> f i-f j) ((eventually_ge_atTop i).mono fun j hj=> h i j hj) tendsto_const_nhds (fun s=>(tendsto_const_nhds (x:=f i s)).sub (hp s)) (fun i=>zero_le_one.trans (hu i))⟩
-- if Prop limits and even Uniform
lemma difference {l:Filter J}[l.NeBot]{q:J→ I→X}{f:I→X}(hp : Tendsto q l (𝓝 p))(hh:∀ᶠ j in l,Sack u (f-q j) L)(he:0≤u):Sack u (f-p) L:=by exact closes hh tendsto_const_nhds (fun i=>(tendsto_const_nhds (x:=f i)).sub (tendsto_pi_nhds.mp hp i)) he
end Sack
end YM.OPE.Flume
