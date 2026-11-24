import YM.GradedFar.Logged.Economy

/-! Through the finite cost operations in G.5. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Economy
open Finset Filter Function Set Spec Table Extraction OPE.Log Asymptotics Orbits
open scoped Topology Classical BigOperators
variable {I J M E A F:Type} [NormedAddCommGroup E][NormedAddCommGroup F]
namespace Paint
variable {Q:Small I} {P:I→ℝ} {x:I→E} (h:Paint Q P x)
lemma linear_c [NormedSpace ℂ E] [NormedSpace ℂ F][FiniteDimensional ℂ E] (L:E→ₗ[ℂ] F) (h:Paint Q P x) : Paint Q P (L ∘ x) := by
    let Y:= LinearMap.toContinuousLinearMap L; have hm:= (Paint.const (Q:=Q) Y).times_cost (y:=L ∘ x) h (Eventually.of_forall fun i=> Y.le_opNorm (x i)); simpa only [one_mul] using hm
lemma linear_r [NormedSpace ℝ E] [NormedSpace ℝ F][FiniteDimensional ℝ E] (L:E→ₗ[ℝ] F) (h:Paint Q P x) : Paint Q P (L ∘ x) := by
    let Y:= LinearMap.toContinuousLinearMap L; have hm:= (Paint.const (Q:=Q) Y).times_cost (y:=L ∘ x) h (Eventually.of_forall fun i=> Y.le_opNorm (x i)); simpa only [one_mul] using hm
lemma product {W:J→ I→ℝ}{x:J→ I→ℂ}(s:Finset J)(h:∀ j∈s,Paint Q (W j) (x j)):Paint Q (fun i=>∏ j∈s,W j i) (fun i=>∏ j∈s,x j i):= by
    induction s using Finset.induction_on with| empty=> simp_rw [Finset.prod_empty]; exact const _| insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact (h i (Finset.mem_insert_self ..)).times (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))
-- use with actual Label prices.
theorem contract [Fintype J][NormedSpace ℂ E]{V : J→ Type}[∀j,NormedAddCommGroup (V j)][∀j,NormedSpace ℂ (V j)] [∀j,FiniteDimensional ℂ (V j)]
    (f:I→MultilinearMap ℂ V E)(hf:∀ w,Paint Q P (fun i=>f i w))(L:J→I→ℝ)(v:I→∀i,V i)
    (h:∀ j,Paint Q (L j) (fun i=> v i j)): Paint Q (fun i=>(∏ j,L j i)*P i) (fun i=> f i (v i)) := by
    let B j:= Fin (Module.finrank ℂ (V j)); let e j: Module.Basis (B j) ℂ (V j):= Module.finBasis ℂ (V j)
    let c (j:J)(k:B j): V j→ₗ[ℂ] ℂ:= (e j).coord k
    -- expansion as in Payroll
    have he(i:I): f i (v i) = ∑ t:((j:J)→ B j), (∏ j, c j (t j) (v i j)) • f i (fun j=> e j (t j)) := by
       have hx:v i= fun j=>∑ k, c j k (v i j) • e j k:=funext fun _=> ((e _).sum_repr ..).symm
       conv_lhs=> rw [hx,MultilinearMap.map_sum_finset]; simp only [MultilinearMap.map_smul_univ]
       apply Finset.sum_congr (by ext; simp) fun _ _=>rfl
    simp_rw [he]; exact Paint.sum _ (fun t _=> (hf _).scales (Paint.product _ (fun j _=> linear_c (c j (t j)) (h j))))
-- rent zero tags or physical
end Paint
end YM.OPE.Logged.Economy
