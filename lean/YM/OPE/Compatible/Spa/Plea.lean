import YM.OPE.Compatible.Spa.Birth
import YM.OPE.Compatible.Spa.Tempo
/-!
# Finite suspension.P. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter
open Drift
open scoped Topology BigOperators Classical
variable {M E F Q:Type}{v:ℝ}{t p:M→ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
lemma PledgeW [NormedAddCommGroup Q][NormedSpace ℝ Q] {f:M→ E→L[ℝ] F}{g:M→ Q→L[ℝ] E}(h:Wealth f t 1)(hp:Wealth g t 1): Wealth (fun i=>(f i).comp (g i)) t 1:= one_mul (1:M→ℝ) ▸ wealth_mul h hp (fun _=> ContinuousLinearMap.opNorm_comp_le ..)
lemma Spot (A:M→ Submodule ℝ F) (f:∀ i,A i→ₗ[ℝ] E) [FiniteDimensional ℝ E](h:∀ x:E,∃ p:∀ i,A i, Wealth (fun i=>(p i).val) t 1∧ ∀ i,f i (p i)=x)(hp:1 ≤ t) :∃ g:(i:M)→ E→ₗ[ℝ] A i, Wealth (fun i=> ((A i|>.subtype).comp (g i)).toContinuousLinearMap) t 1 ∧ ∀ i x,f i (g i x)=x:=by
     obtain ⟨p,hP,hx⟩:= RiftCost A (fun _=>⊤) f ⊤ (by
        intro x _; obtain ⟨z,hz,h⟩:=h x; exact ⟨z,hz,fun i=> ⟨Submodule.mem_top,h i⟩⟩) hp (zero_le_one:(0:M→ℝ)≤1)
     let Q:= Submodule.topEquiv (R:=ℝ) (M:=E); refine ⟨fun i=> (p i).comp Q.symm.toLinearMap, ?_, fun i x=>?_⟩ -- typeclass top norm
     · apply Scooped _ _ hp zero_le_one; intro x; exact (one_mul (1:M→ℝ)) ▸ wealth_mul hP (wealthC (Q.symm x)) (fun i=> (((A i).subtype.comp (p i)).toContinuousLinearMap).le_opNorm _) 
     exact (hx i (Q.symm x)).2
noncomputable abbrev drainU (A:E→ₗ[ℝ] F)(σ:F→ₗ[ℝ] F): Jewel E→ₗ[ℝ] F:= (A.comp (LinearMap.proj 0)) + σ.comp (A.comp (LinearMap.proj 1))+σ.comp (σ.comp (A.comp (LinearMap.proj 2)))
lemma drain_wϕ (p:E→ₗ[ℝ] F)(σ:F→ₗ[ℝ] F)(X:Jewel E) : drainU p σ X=p (X 0)+ σ (p (X 1))+σ (σ (p (X 2))):=rfl
lemma drain_gap (p:E→ₗ[ℝ] F)(σ:F→ₗ[ℝ] F)(X:Jewel E)(h:∀ x,σ (σ (σ (p x)))=0):σ (drainU p σ X)=drainU p σ (τΓ E X):=by
     rw [drain_wϕ,drain_wϕ,map_add,map_add, h]; simp only [(τRide X).1,(τRide X).2.1,(τRide X).2.2,map_zero,zero_add, add_zero]
lemma τwrite (x:Jewel E): Pi.single 0 (x 0)+τΓ _ (Pi.single 0 (x 1))+τΓ _ (τΓ _ (Pi.single 0 (x 2)))=x:=by
     funext i;fin_cases i<;>simp [τΓ, Matrix.vecHead, Matrix.vecTail]
lemma convU' (A:E→ₗ[ℝ] F)(f:F→ₗ[ℝ] (Jewel E))(q:F→ₗ[ℝ] F)(he:∀ x:E,f (A x)=Pi.single 0 x)(hv:∀ x:F, f (q x)=τΓ E (f x))(X:Jewel E): f (drainU A q X)=X:=by rw [drain_wϕ,map_add,map_add, hv,hv,hv,he,he,he]; exact τwrite X
lemma drain_cost [FiniteDimensional ℝ E](g:M→E→ₗ[ℝ] F)(hp:1 ≤ t)(A:M→Submodule ℝ F)(f:∀ i,A i→ₗ[ℝ] A i)(p':∀ i,E→ₗ[ℝ] A i)(U:F→L[ℝ] F)(hx:∀ i x,(f i x).val=U x.val)(h:Wealth (fun i=> (g i).toContinuousLinearMap) t 1)(hh:∀ i x,(p' i x).val= g i x): Wealth (fun i=> ((A i|>.subtype).comp (drainU (p' i) (f i))).toContinuousLinearMap) t 1:=by
     refine Scooped _ (fun x=>?_) hp zero_le_one; change Wealth (fun i=>(drainU (p' i) (f i) x).val) _ _; simp_rw[drain_wϕ,Submodule.coe_add,hx,hh]; have hv(i:Fin 3):Wealth (fun j=> g j (x i)) t 1:= by exact one_mul (1:M→ℝ) ▸ wealth_mul h (wealthC (x i)) fun j=> (g j).toContinuousLinearMap.le_opNorm _
     exact anthW hp zero_le_one (anthW hp zero_le_one (hv 0) (aimW U (hv 1))) (aimW U (aimW U (hv 2)))
end YM.OPE.Hark
