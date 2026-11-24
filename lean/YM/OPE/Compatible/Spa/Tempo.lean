import YM.OPE.Compatible.Spa.CO
/-!
# Priced collections of variable flag. Finite witnesses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter ContinuousLinearMap NormedSpace Finset
open Drift
open scoped Topology BigOperators Classical
variable {M E F Q Z:Type}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ E]
variable {t k Z:M→ℝ}{u:M→ E→L[ℝ] F}
lemma Scooped (U:M→E→ₗ[ℝ] F) (hp:∀ x:E,Wealth (fun i=>U i x) t k)(ht:1 ≤ t)(hk:0 ≤ k): Wealth (fun i=>(U i).toContinuousLinearMap) t k:=by
    let C (w:M):= (U w).toContinuousLinearMap; apply grantV C _ ht hk; let I:=Fin (Module.finrank ℝ E); let B:=Module.finBasis ℝ E; let W:= M × (Metric.closedBall (0:E) 1); let X(n:I)(i:W):= (B.coord n).toContinuousLinearMap i.2.val; let p:W→ M:=Prod.fst; have hx(n:I):Wealth (fun i:W=>C i.1 (B n)) (t ∘ p) (k ∘ p):=by
       obtain ⟨c,hc,k,h⟩:= hp (B n); exact ⟨c,hc,k,fun i=>h i.1⟩
    have hy: Wealth (fun i:W=> i.2.val) (t ∘ p) 1:=⟨1,zero_le_one,0,fun i=>by have hh:= i.2.property; simpa only [Metric.mem_closedBall,dist_zero_right,mul_one, pow_zero,Pi.one_apply] using hh⟩ -- h lint
    have hv(n:I):Wealth (fun i:W=> X n i • (C i.1 (B n))) (t ∘ p) (k ∘ p):=one_mul (k ∘ p) ▸ (wealth_mul (aimW (B.coord n|>.toContinuousLinearMap) hy) (hx n) (g:=fun i=> X n i • (C i.1 (B n))) fun _=>le_of_eq (norm_smul ..)); have he(i:W): C i.1 i.2.val=∑ n:I, X n i • (C i.1 (B n)):=by
        calc
          _= C i.1 (∑ n:I,X n i • B n):=by rw [show (∑ n:I,X n i • B n)= i.2.val from B.sum_repr _]
          _ = _:= by rw[map_sum]; simp_rw [(C i.1).map_smul]
    simp_rw[he]; exact wealthset Finset.univ _ (fun i _=>hv i) (fun i=>ht _) (fun i=>hk _)
-- section data paid all starts. F norm locus
lemma RiftCost (A P:M→ Submodule ℝ F) (f:∀ i,A i→ₗ[ℝ] E) (X:Submodule ℝ E)(h:∀ x∈X,∃ p:(i:M)→ A i, Wealth (fun i=>(p i).val) t k ∧∀ i,(p i).val∈P i∧ f i (p i)=x)(ht:1 ≤ t)(hk: 0 ≤ k):∃ U: (i:M)→ X→ₗ[ℝ] A i, Wealth (fun i=> ((A i|>.subtype).comp (U i)).toContinuousLinearMap) t k ∧∀ i x,(U i x).val∈ P i ∧ f i (U i x)=(x:X).val:=by
      let B:=Module.finBasis ℝ (↥X); let I:=Fin (Module.finrank ℝ (↥X)); choose p hp hP using fun n:I=> h _ (B n|>.property); let T(n:I)(w:M): X→ₗ[ℝ] A w:= (B.coord n).smulRight (p n w); let C (w):= ∑ i:I,T i w
      have hv(i:M)(x:X): (C i) x=∑ n:I,(B.coord n x) • p n i:=by unfold C;rw[LinearMap.sum_apply]; rfl
      refine ⟨C,Scooped _ (fun x=>?_) ht hk,fun i x=>?_ ⟩
      · change Wealth (fun i=>(C i x).val) _ _; simp_rw [hv,Submodule.coe_sum]; exact wealthset Finset.univ _ (fun i _=>scaleD (k:=B.coord i x) (hp i)) ht hk
      rw [hv,map_sum]; refine ⟨?_,?_⟩
      · rw [Submodule.coe_sum]; exact (P i).sum_mem (fun j _=> (P i).smul_mem _ (hP j i).1)
      calc
        _= ∑ n:I,(B.coord n x) • (B n).val:= sum_congr rfl (fun j _=>by rw[map_smul,(hP j i).2])
        _= X.subtype (∑ n:I,(B.coord n x) • B n):=by rw[map_sum]; rfl
        _ = _:= by rw [show (∑ n:I,(B.coord n x) • B n)=x from B.sum_repr _];rfl
end YM.OPE.Hark
