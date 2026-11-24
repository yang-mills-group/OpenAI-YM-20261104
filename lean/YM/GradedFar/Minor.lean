import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
/-!
# Finite determination, near leading on that aperture
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set
open scoped Topology BigOperators Classical
variable {E F I X:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
   [NormedAddCommGroup F] [NormedSpace ℝ F]{l:Filter X}
-- standard finite-dimensional reduction similar XSpace/Normalize/Forecast.finalists
private lemma fin_select (L:I→E→L[ℝ]ℂ) (H:∀ x:E,(∀ i,L i x=0)→ x=0):
    ∃ s:Finset I,LinearMap.ker (LinearMap.pi (fun i:↥s=> (L i.val).toLinearMap))=⊥:=by
 let A(s:Finset I):= LinearMap.pi fun i:↥s=> (L i.val).toLinearMap; let K(s:Finset I):=LinearMap.ker (A s)
 have hh(x)(s:Finset I): x∈ K s ↔ ∀ i∈s,L i x=0:= by simp [K,A,funext_iff]
 have he:∃ n:ℕ,∃ s:Finset I,Module.finrank ℝ (K s)=n:=⟨_,∅,rfl⟩; obtain ⟨s,hs⟩:=Nat.find_spec he
 refine ⟨s, le_antisymm (show K s≤⊥ from ?_) bot_le⟩; intro x hx; apply (Submodule.mem_bot ..).mpr; refine H x (fun i=>?_ )
 let t:Finset I:=insert i s; have hv: K t ≤ K s:= fun x hx=> (hh x s).mpr fun j hj=>(hh x t).mp hx j (Finset.mem_insert_of_mem hj)
 have h₀:=Submodule.eq_of_le_of_finrank_le hv (hs ▸ Nat.find_min' he (show ∃ s:Finset I,Module.finrank ℝ (K s)=Module.finrank ℝ (K t) from ⟨t,rfl⟩))
 exact (hh x t).mp (h₀ ▸ hx) i (Finset.mem_insert_self ..) -- direction rewrite
lemma plan_lim {L:X→E→L[ℝ] F}{K:E→L[ℝ] F}(h:∀ b:E,Tendsto (fun i=> L i b) l (𝓝 (K b))): Tendsto L l (𝓝 K):=by
 let b:=Module.finBasis ℝ E; let c i:= ContinuousLinearMap.smulRightL ℝ E F (b.coord i).toContinuousLinearMap
 have he(f:E→L[ℝ]F): f=∑ i,c i (f (b i)):=by
   ext x; conv_lhs=> rw [← b.sum_repr x,map_sum];
   rw [_root_.sum_apply]; exact Finset.sum_congr rfl fun i _=> map_smul ..
 nth_rw 1 [he K]; apply Tendsto.congr' _ (tendsto_finsetSum Finset.univ (fun i _=> (c i).continuous.continuousAt.tendsto.comp (h (b i))))
 exact Eventually.of_forall fun i=>(he _).symm
lemma issued (L:I→E→L[ℝ]ℂ) {K:X→I→E→L[ℝ]ℂ}(H:∀ x:E,(∀ i,L i x=0)→x=0)
    (h:∀ i x, Tendsto (fun p=>K p i x) l (𝓝 (L i x))): ∃ s:Finset I,∃ C:ℝ,0≤C ∧ ∀ᶠ i in l,∀ x:E,
      ‖x‖ ≤ C*‖(fun j:↥s=> K i j.val x)‖ := by
 obtain ⟨s,H0⟩:= fin_select L H; let Q:= (↥s)→ℂ; let B:=ContinuousLinearMap.pi (fun i:↥s=>L i.val); let A(i:X):= ContinuousLinearMap.pi (fun j:↥s=> K i j.val)
 let R:= (B.toLinearMap.leftInverse).toContinuousLinearMap; have hr(x:E): R (B x)=x:= LinearMap.leftInverse_apply_of_inj (f:=B.toLinearMap) H0 x
 let C:=max 1 ‖R‖; have hC:0<C:=lt_of_lt_of_le zero_lt_one (le_max_left ..); have hp(x:E):‖x‖ ≤ C*‖B x‖:= ((hr x) ▸ (R.le_opNorm (B x))).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _))
 have hv:= plan_lim (l:=l) (K:=B) (L:=A) (fun x=> tendsto_pi_nhds.mpr fun i=> h i.val x); refine ⟨s,2*C,by positivity,?_ ⟩
 filter_upwards [ (show Tendsto (fun i=> ‖B-A i‖) l (𝓝 0) from (by simpa only [sub_self,norm_zero] using ((tendsto_const_nhds (x:=B)).sub hv).norm)).eventually_le_const (show 0<(2*C)⁻¹ by positivity)] with i hi x
 let δ:=(2*C)⁻¹; have hc : ‖B x‖ ≤ δ*‖x‖ + ‖A i x‖:=by
   rw [show B x=(B-A i) x+A i x from (by rw [_root_.sub_apply,sub_add_cancel])]; exact (norm_add_le ..).trans (add_le_add
      (((B-A i).le_opNorm x).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))) le_rfl)
 specialize hp x; obtain hp:= hp.trans (mul_le_mul_of_nonneg_left hc hC.le)
 rw [mul_add,← mul_assoc, show C*δ=1/2 from (by unfold δ; field_simp)] at hp
 change _ ≤ _*‖A i x‖; linarith only [hp]
end YM.Integration.GradedFar.Tariff.Billboard
