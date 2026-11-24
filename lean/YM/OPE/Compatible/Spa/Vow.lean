import YM.OPE.Compatible.Spa.Plea
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
variable [FiniteDimensional ℝ E]
-- Shape engine
lemma RexE (B:M→ Submodule ℝ F) (X:∀ m,B m→ₗ[ℝ] Jewel E)(U:F→L[ℝ] F)(he:∀ x,U (U (U x))=0)(hq:1 ≤ t)(h:∀ x:Jewel E,∃ g:(i:M)→B i, Wealth (fun i=>(g i).val) t 1 ∧∀ i, X i (g i)=x)
    (hp:∀ m,∃ v:B m→ₗ[ℝ] B m,(∀ x,(v x).val=U x.val)∧∀ x,X m (v x)=τΓ E (X m x)):∃ Y:(m:M)→Jewel E→ₗ[ℝ] B m,Wealth (fun i=> ((B i|>.subtype).comp (Y i)).toContinuousLinearMap) t 1 ∧ (∀ i x,X i (Y i x)=x)∧∀ i x,U ((Y i x).val)= (Y i (τΓ E x)).val:=by
      obtain ⟨a,ha,W⟩:= Spot B X h hq; let S:=LinearMap.single ℝ (fun _:Fin 3=> E) 0; let f(i):=(a i).comp S; choose T hV hT using hp; let u(i):=drainU (f i) (T i); refine ⟨u, drain_cost (fun i=>(B i|>.subtype).comp (f i)) hq B T f U hV ?_ (fun _ _=>rfl),fun i=>convU' (f i) _ _ (fun x=>W i (S x)) (hT i),fun i x=>?_⟩
      · apply Scooped _ (fun x=>?_) hq zero_le_one; exact one_mul (1:M→ℝ) ▸ wealth_mul ha (wealthC (S x)) (fun i=>(((B i|>.subtype).comp (a i)).toContinuousLinearMap).le_opNorm (S x))
      rw [←hV i]; unfold u; congr 1; refine drain_gap _ _ _ fun w=>Subtype.ext ?_; change _= (0:F); rw [hV,hV,hV]; exact he _
-- Wealth.app L. continuous proof.Transport Λ
omit [FiniteDimensional ℝ E] in lemma PayF {Q:Type}[NormedAddCommGroup Q][NormedSpace ℝ Q][FiniteDimensional ℝ Q] (L:Q≃ₗ[ℝ] F) (A:F→ₗ[ℝ] E) {v:M→F}(hp:Wealth v t p): Wealth (fun i=>A (v i)) t p:=by
     letI := FiniteDimensional.of_surjective L.toLinearMap L.surjective; exact aimW (A.toContinuousLinearMap) hp
end YM.OPE.Hark
