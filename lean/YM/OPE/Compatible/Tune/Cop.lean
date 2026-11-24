import YM.OPE.Compatible.Tune.Frames
/-!
# Flag ledger. compressed.P
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter Finset
open Drift
open scoped Topology BigOperators Classical
variable {d:ℕ}{V:Fin d→Type}{M E Q:Type}{v:ℝ}{t p:M→ℝ}{ρ:ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E]
variable [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)]
-- `read F→ Tokens`. Lift provided ζ.Price. specific Veins inputs
variable {A:ℕ→ M→Submodule ℝ E}{Y:M→ Submodule ℝ E}{X:(e:Fin d)→(m:M)→ A e.val m→ₗ[ℝ] Jewel (V e)}{g:E→ₗ[ℝ] E}{R:(e:Fin d)→(m:M)→ Jewel (V e)→ₗ[ℝ] A e.val m}
namespace Pipes
variable (H:Pipes A Y X g R)
section
variable {H}[∀ i,FiniteDimensional ℝ (V i)] {p:M→ℝ}
variable (F:Charge H p)
variable {W:Fin d→Type}[∀ i,NormedAddCommGroup (W i)][∀ i,NormedSpace ℝ (W i)] [∀ i,FiniteDimensional ℝ (W i)]
variable (K:(i:Fin d)→Jewel (V i)≃ₗ[ℝ] Jewel (W i))
local notation "S!"=> Mel V
noncomputable def Sentinel (m:M): E→L[ℝ] Mel W:=by
       let vρ:= F.CLt.choose m; exact (honors K).toLinearMap.toContinuousLinearMap.comp vρ -- reserved word
omit [∀ i,FiniteDimensional ℝ (W i)] in
lemma intent (m:M)(x:E): Sentinel F K m x=honors K (port H m x):=by
       suffices h: F.CLt.choose m x=port H m x from congr_arg (honors K) h
       exact DFunLike.congr_fun (F.CLt.choose_spec.2 m) x
omit [∀ i,FiniteDimensional ℝ (W i)] in
lemma reliant : Wealth (fun m=> Sentinel F K m) p 1:=by
       exact PledgeW (wealthC (honors K|>.toLinearMap.toContinuousLinearMap)) F.CLt.choose_spec.1
noncomputable def ScaledB (R:(e:Fin d)→(m:M)→Jewel (V e)→ₗ[ℝ] A e.val m) (m:M) : Mel W→L[ℝ] E:= ((bulk R m).comp (honors K).symm.toLinearMap).toContinuousLinearMap
lemma FitSea (m:M)(x:Mel W): Sentinel F K m (ScaledB K R m x)=x:=by rw[intent]; change honors K (port H m (bulk R m _))=_; rw[H.worthM m|>.len]; exact (honors K).apply_symm_apply _
include F
lemma SeaCost : Wealth (fun m=>ScaledB K R m) p 1:=by
     let f:= honors K; change Wealth (fun j=> (((bulk R j).comp f.symm.toLinearMap)).toContinuousLinearMap) _ _; apply Scooped _ (fun x=>?_) F.keep zero_le_one; exact one_mul (1:M→ℝ) ▸ wealth_mul (Pipes.Bucks H F) (wealthC (f.symm x)) (fun i=> (Buck (R:=R) i).le_opNorm _)
omit [∀ i,FiniteDimensional ℝ (W i)] in
lemma Mercy (m:M)(x:E): x∈Bay A Y d m ↔ Sentinel F K m x=0:=by rw[intent,LinearEquiv.map_eq_zero_iff]; exact H.worthM m|>.hero _
omit [∀ i,FiniteDimensional ℝ (W i)] in
lemma κSym (m:M)(v:(i:Fin d)→ V i≃ₗ[ℝ] W i)(hp:∀ i,Honest (K i) (v i))(x:E): Sentinel F K m (g x)= FlowP W (Sentinel F K m x):=by rw [intent,intent, H.portτ m]; exact troop K v hp _
end
end Pipes
end YM.OPE.Hark
