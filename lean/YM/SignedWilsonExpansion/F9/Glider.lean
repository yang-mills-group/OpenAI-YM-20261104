import YM.SignedWilsonExpansion.F9.Empathy
/-!
# Stable left inverse in scalar prices.Asym.γ.All frequencies sequential.
Proof is for any Banach target finite channels. We may chop down to finite anytime.
-/
noncomputable section
set_option autoImplicit false
namespace YM.SignedWilsonExpansion.Commission
open WilsonCoeffUV.Bank Function Filter Set
open scoped BigOperators Topology ContDiff Classical
variable {ι κ σ σ' E F K:Type} [NontriviallyNormedField K][CompleteSpace K][AddCommGroup E][Module K E]
variable [NormedAddCommGroup F][NormedSpace K F]
variable {l:Filter ι}{q:ι→ℝ}
namespace Foundation
-- stable left by pointwise.For perturb all rows. Need finite target. Real/Complex same axioms.
section fin
variable [Fintype κ] (B:Module.Basis κ K E)
variable (P: E →ₗ[K]F)(U:ι→E→ₗ[K]F)
variable (h: Injective P) (v:∀ i:κ, Tendsto (fun j=> U j (B i)) l (𝓝 (P (B i))))
variable [FiniteDimensional K F]
include h v
lemma shore : ∃ Q:ℝ,0<Q ∧ ∀ᶠ j in l,∀ x:E, ‖B.equivFun x‖ ≤ Q*‖U j x‖:=by
    let C:=B.equivFun.toLinearMap ∘ₗ P.leftInverse; have hc(x): C (P x)=B.equivFun x:=by unfold C; rw [LinearMap.comp_apply,LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr h)] ; rfl
    let D : F→L[K] (κ→K):= C.toContinuousLinearMap; let Q:=max 1 ‖D‖; let S j:=B.equivFun.toLinearMap-C ∘ₗ U j; have hv(i:κ): Tendsto (fun j=> ‖S j (B i)‖) l (𝓝 0):=by
        have he : Tendsto (fun j=>S j (B i)) l (𝓝 ( B.equivFun (B i)-C (P (B i)))):= tendsto_const_nhds.sub (D.continuous.continuousAt.tendsto.comp (v i)); rw [hc,sub_self] at he; simpa only [norm_zero] using he.norm
    have hV: Tendsto (fun j=>∑ x:κ, ‖S j (B x)‖) l (𝓝 0):=(by simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _=> hv i)); have hq:0<Q:=lt_of_lt_of_le zero_lt_one (le_max_left ..); refine ⟨Q*2,by positivity,?_⟩; filter_upwards [hV.eventually_le_const (show (0:ℝ)<1/2 by norm_num)] with i hi x -- check lemma
    let y:= ‖B.equivFun x‖; let t:=B.equivFun x; have hy:0≤ y:= norm_nonneg _
    have ht:‖S i x‖≤ y*(1/2):=by
       nth_rw 1 [← B.sum_repr x,map_sum]; refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun a=>y*‖S i (B a)‖) fun a _=>?_ ) ?_)
       · rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_right (norm_le_pi_norm t a) (norm_nonneg _)
       rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hi hy
    have hp: ‖S i x+ D (U i x)‖= y:=by change ‖B.equivFun x - D (U i x)+ D (U i x)‖ = _; rw [sub_add_cancel]
    have hf:= hp.symm.trans_le (norm_add_le ..); have hg:= hf.trans ( add_le_add ht ((D.le_opNorm _).trans (mul_le_mul_of_nonneg_right (show ‖D‖ ≤ Q from le_max_right ..) (norm_nonneg _)))); change y≤_; linarith
end fin
variable (P: σ→ E →ₗ[K] F)
-- preserve `Purchase` finite reps at all orders η.Take a *concrete* finite subset, receipts.Timeline monetary.
lemma cutB {K':Type*} [DivisionRing K']{E':Type*} [AddCommGroup E'] [Module K' E'][FiniteDimensional K' E'] (P: σ→Submodule K' E'):∃ S:Finset σ, (⨅ i:S,P i.val)=⨅ i,P i:=by
    let U(s:Finset σ):= ⨅ i:s,P i.val; have he : ∃ n:ℕ,∃ s:Finset σ,Module.finrank K' (U s)=n:=⟨_,∅,rfl⟩; obtain ⟨s,hs⟩:=Nat.find_spec he; refine ⟨s,le_antisymm ?_ (le_iInf (fun i=> iInf_le P i.val))⟩; apply le_iInf; intro i; have hp:U (insert i s) ≤ U s:= le_iInf fun j=> iInf_le_of_le (⟨j.val,Finset.mem_insert_of_mem j.property⟩:(insert i s:Finset σ)) le_rfl
    have hv:U (insert i s)=U s:= Submodule.eq_of_le_of_finrank_le hp (hs ▸ Nat.find_min' he (show ∃ t:Finset σ,Module.finrank K' (U t)=Module.finrank K' (U (insert i s)) from ⟨_,rfl⟩)); change U s≤ _; rw [← hv]; exact iInf_le_of_le (⟨i,Finset.mem_insert_self ..⟩:(insert i s:Finset σ)) le_rfl
variable [FiniteDimensional K E][FiniteDimensional K F]
variable (U:ι→ σ→E→ₗ[K]F)(h:∀ x:E,(∀ i,P i x=0)→ x=0)(v:∀ i (x:E), Tendsto (fun j=> U j i x) l (𝓝 (P i x)))
include h
lemma cuts : ∃ S:Finset σ,Injective (LinearMap.pi (fun i:S=> P i.val)):=by obtain ⟨S,hS⟩:= cutB (fun i=> LinearMap.ker (P i)); refine ⟨ S,LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr (fun p w=> ?_))⟩; have he:= LinearMap.mem_ker.mp w; have hv: p∈ ⨅ i,LinearMap.ker (P i):=(by rw [← hS]; exact (Submodule.mem_iInf _).mpr fun i=> LinearMap.mem_ker.mpr (congr_fun he i)); exact (Submodule.mem_bot ..).mpr (h _ (fun i=> LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hv i)))
-- index σ convergence then all estimates.Applicable finite list of valid queries even if arity zero.
variable [Fintype κ]
include v
lemma projects (B:Module.Basis κ K E): let S:= (cuts P h).choose;∃ Q:ℝ,0<Q∧∀ᶠ i in l,∀ x:E,‖B.equivFun x‖ ≤ Q* ‖(fun j:S=> U i j.val x)‖:=by
    intro S; let V(i:ι):= LinearMap.pi (fun j:S=> U i j.val); exact shore (F:=S→ F) B _ V (cuts P h).choose_spec (fun i=> tendsto_pi_nhds.mpr fun j=> v j.val (B i))
lemma costs (u:Maxer l q)(x:ι→ E)(X:∀ i∈ (cuts P h).choose,Billed l q (fun j=> U j i (x j))): Across l q K x:=by
    let B:=Module.finBasis K E; obtain ⟨Q,hQ,H⟩:= projects P U h v B -- thermostat arg
    let Y(j:ι)(i: (cuts P h).choose):= U j i.val (x j); have he : Billed l q Y:= Billed.pi u _ (fun i=> X i.val i.property); apply Across.basisN u B; exact Billed.room (BoundPoly.mulP u (BoundPoly.pureP Q) he (Eventually.of_forall (fun j=>norm_nonneg _))) (H.mono fun i p=> p (x i))
end Foundation
end YM.SignedWilsonExpansion.Commission
