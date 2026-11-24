import YM.OPE.Compatible.Grove.Quill
/-!
# Principal ray geometry. Rank read by evaluating arbitrary mixtures of jets in weights. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Work.G05 WardBin Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
section
variable {Z:Type}[NormedAddCommGroup Z][NormedSpace ℝ Z][Fintype I]
private lemma mix_lead (f: Z→ℝ)(k:ℕ)(F:ℝ→Z)(h:ContDiffAt ℝ k f 0)(hf:ContDiffAt ℝ k F 0)(hp:F 0=0): leading k (f∘F)=∑ i∈ Finset.range (k+1), leading k ((Tensor.diagonal (Tensor.coeff f i 0)) ∘ F):=by
    have he:=jets_comp hf hf (show ContDiffAt ℝ k f (F 0) by rw [hp]; exact h) ((blockTaylor_contDiff k f _).contDiffAt) rfl (fun _ _=>rfl) (fun i hi=> show _= _ from ((hp.symm ▸ (show _= _ from (blockTaylor_jets h i hi)))|>.symm)) k le_rfl -- expected
    rw [show leading k (f ∘ F) = leading k (blockTaylor k f∘ F) from ?_]; swap; · unfold leading iteratedDeriv; rw [he]
    rw [show blockTaylor k f ∘ F=(fun x=>∑ i∈range (k+1), Tensor.diagonal (Tensor.coeff f i 0) (F x)) from funext (fun x=>by simp only [Function.comp_apply,blockTaylor,Finset.sum_apply])]; exact lead_sum _ _ fun i _=> (Tensor.diag_smooth _ _).contDiffAt.comp _ hf

private lemma layered_lead (A:Tensor.T Z ℝ n)(p:I→Z)(u:I→ℕ)(k:ℕ): leading k (Tensor.diagonal A ∘ (fun t:ℝ=> ∑ i,t^(u i) • p i))=∑ y:Fin n→I, if (∑ j,u (y j))=k then A (fun j=> p (y j)) else 0:=by
    have hx(t:ℝ):Tensor.diagonal A (∑ i,t^(u i) • p i)=∑ y:Fin n→I, t^(∑ j,u (y j)) • (A (fun j=> p (y j))):=by
       rw [Tensor.diagonal,A.map_sum (fun _ i=> t^(u i) • p i)]; apply sum_congr rfl; intro i _; rw [A.map_smul_univ, Finset.prod_pow_eq_pow_sum]
    rw [show Tensor.diagonal A ∘ _ = (fun t:ℝ=> ∑ y: Fin n→I,t^(∑ j,u (y j)) • (A (fun j=> p (y j)))) from funext hx]; rw [lead_sum]; swap; · intro i _; exact (monoSmooth _ _ _).contDiffAt
    apply sum_congr rfl; intro j _; rw [lead_monomial]; simp [eq_comm]
end
variable [Fintype I]
def spout (x:I→fieldX W)(k:I→ℕ)(t:ℝ): fieldX W:=∑ j,t^(k j+1) • x j
def slopeX (x:I→fieldX W)(k:I→ℕ)(v n:ℕ)(p:Script W n):ℝ:=∑ i:Fin n→I, if (∑ j,(k (i j)+1))=v then wholeX p (x ∘ i) else 0
lemma pulses (p:Chant G n)(x:I→fieldX (Shade G))(k:I→ℕ)(r:ℕ): leading r (fun t:ℝ=> verseX p (lotU (spout x k t)))=∑ j∈range (r+1), slopeX x k r j (coff p j):=by
    let v(i):=collectQ p (x i); let F(t:ℝ):= ∑ i,t^(k i+1) • v i; have he(t:ℝ):verseX p (lotU (spout x k t))=permit p (F t):=by rw [← permit_atom]; unfold spout; rw [map_sum];simp_rw [map_smul];rfl
    rw [funext he]; let u: I→ℕ:= fun i=>k i+1; change leading r (permit p∘ F) = _; rw [mix_lead]; rotate_left
    · exact (permitS p).contDiffAt.of_le le_top
    · exact ContDiffAt.sum (f:=fun i (t:ℝ)=> t^(u i) • v i) (fun i _=> (monoSmooth ..).contDiffAt)
    · unfold F; apply Finset.sum_eq_zero; intro i _; rw [zero_pow (by omega), zero_smul]
    refine Finset.sum_congr rfl fun j _=> ?_; rw [show leading r _=_ from layered_lead (Tensor.coeff (permit p) j 0) v u r]; apply Finset.sum_congr rfl; intro i _; simp_rw [coinReads];rfl
end Script
end YM.OPE.Flume
