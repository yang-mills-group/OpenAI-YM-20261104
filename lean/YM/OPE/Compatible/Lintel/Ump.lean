import YM.OPE.Compatible.Lintel.Prime
/-!
# Hearing valuation. Winding bill at every income. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n m c f:Side}{S:StepData c f}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}
namespace Script
open Page Virgin
variable [Fintype I][Fintype J]
lemma norm_le_field (A:Row J I)(hp:Whole A):∃ C:ℝ,0 ≤ C∧∀ (n:Side)(x:deck I n),‖A.acts n*ᵥ x‖ ≤ C*(n.val:ℝ)^4*‖x‖:=by
    obtain ⟨s,D,hs,H⟩:=hp; let M:= max D 0; have hm:0 ≤ M:= le_max_right ..; refine ⟨Fintype.card I*M,by positivity,fun n x=> (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=> ?_⟩
    have ht(j:Tab I n): ‖A.acts n i j‖≤ M:=by
       let f(z:Cover):=if j.1=i.1+wrap n z then A i.2 j.2 z else 0; change ‖∑' z,f z‖ ≤ M
       have hk z: ‖f z‖ ≤ ‖A i.2 j.2 z‖:=by unfold f; split; exact le_rfl; simp
       obtain ⟨-,ha,he⟩:= (H i.2 j.2).unweighted hs.le; have hS : Summable f:=ha.of_norm_bounded hk; exact (norm_tsum_le_tsum_norm hS.norm).trans ((hS.norm.tsum_le_tsum hk ha).trans (he.trans (le_max_left ..)))
    unfold mulVec dotProduct; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> M*‖x‖) (fun j _=> show ‖A.acts n i j*x j‖≤ M *‖x‖ by rw [norm_mul]; exact mul_le_mul (ht j) (norm_le_pi_norm x j) (norm_nonneg _) hm)).trans_eq ?_)
    rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_prod,Lattice.site_card]; push_cast; ring -- frob open x Pi? x not matrix
lemma treasuryT {p:Script J r}{q:∀ n:Side,(Fin r→deck J n)→ℝ}(A:Row J I)(h:Whole A) (hb:folk p)(hx:∀ d,treasury p q d): treasury (raft A p) (fun i x=> q i fun j=> A.acts i *ᵥ x j) t:=by
    obtain ⟨D,hd,H⟩:=norm_le_field A h; obtain ⟨c,hc,P⟩:=hx (4*r+t); refine ⟨c*D^r,by positivity,fun i x=>?_⟩
    rw [raftReads _ h _ (folk_whole hb)]; let z:ℝ:= i.val; let v:= z^(4*r); have hv:0 < v:=pow_pos (show 0 < z from Nat.cast_pos.mpr i.pos) _; let Y:=fun j=> (A.acts i)*ᵥ x j; apply le_of_mul_le_mul_left _ hv -- left
    rw [← mul_assoc v]; rw [show v*z^t=z^(4*r+t) by unfold v; rw [pow_add]]; refine (P i Y).trans ((mul_le_mul_of_nonneg_left (prod_le_prod (s:=univ) (g:=fun j=>D*(z^4)*‖x j‖) (f:=fun j=>‖Y j‖) (fun k _=> norm_nonneg _) (fun j _=>H i (x j))) hc).trans_eq ?_);rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]; unfold v; ring
lemma treasuryR (p:Script I r)(t:ℕ):treasury p (fun n v=>library n p v) t:=⟨0,le_rfl,fun i x=>by simp⟩
end Script
end YM.OPE.Flume
