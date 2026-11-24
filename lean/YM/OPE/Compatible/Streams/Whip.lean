import YM.OPE.Compatible.Streams.Belt
/-! # Wheel.Trans ports for B horizons -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
variable {p:(∀ i:Fin s,E i) →L[ℝ] (∀ i:Fin s,E i)}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{a w:H→ℝ}{f g:H→ℕ→ Mints E}
variable {X:Mints E→L[ℝ] Mints E}
namespace Eave
variable {θ:ℝ}(U:Eave L X T a r θ u k)
include U
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)]
lemma globalCost : Wealth (fun i=> ‖U.PO i‖) a 1:=by
    let M:= Σ i:H, Lingo r (L i); let V:=U.annex (Sigma.fst:M→ H); let z(i:M):=i.snd; let F(i:M):=‖z i‖; have hv: Wealth (fun i:M=>(z i).val) (a∘Sigma.fst) F:=⟨1,zero_le_one,0,fun _=>by rw [pow_zero,one_mul,one_mul]; rfl⟩; have he:=V.Station z hv (fun i=> (norm_nonneg _ : 0 ≤ ‖i.snd‖)); obtain ⟨c,hc,k,H⟩:= he.1; refine ⟨c,hc,k,fun i=>?_⟩; dsimp only; rw [Real.norm_of_nonneg (norm_nonneg (U.PO i)),Pi.one_apply,mul_one]; apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hc (pow_nonneg (zero_le_one.trans (U.fits i)) k)); intro x; rw [show U.PO i x=_ from (show _= V.PO (Sigma.mk i x) x from U.slotInv (Sigma.fst:M→_) (⟨i,x⟩:M) x)]; exact H ⟨i,x⟩
omit [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][FiniteDimensional ℝ (G k)] in
lemma beside (i:H): Lingo θ (L i) ≤ Lingo r (L i):=by
    intro p h; obtain ⟨c,hc⟩:=h; exact ⟨c, Hex.warm hc U.ThetaPitch U.tier⟩
include U
lemma OpFee : ∃ C:ℝ,0 ≤ C ∧∃ k':ℕ,∀ i:H,∀ x:Lingo r (L i),‖(U.PO i x).val‖≤ C*a i^k'*‖x.val‖:=by
     obtain ⟨c,hc,k,H⟩:= globalCost U; refine ⟨c,hc,k,fun i x=>?_⟩; have hh:=H i; dsimp only at hh; rw [Real.norm_of_nonneg (norm_nonneg (U.PO i)),Pi.one_apply,mul_one] at hh; exact (le_opNorm (U.PO i) x|>.trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _)))
end Eave
-- Shift difference polynomial. Extend Filters. thick multiplication.
variable {F:Type}[NormedAddCommGroup F]
lemma parkT {p:ℕ→ F}(n:ℕ)(hp:Thick r (fun i=>p (i+n))) :Thick r p:=by
     obtain ⟨q,hq,hx,c,hC⟩:= hp.Bill; obtain ⟨t,ht,hv⟩:=exists_between hx; have ha:=lt_of_le_of_lt hq ht; have ht': Hex t (fun i=>p (i+n)) c:= Hex.warm hC hq ht.le; apply Variance.polyZ p ha _ hv; refine ⟨c/t^n,?_⟩; filter_upwards [eventually_ge_atTop n] with i hi; have he:= ht' (i-n); dsimp only at he; rw [Nat.sub_add_cancel hi] at he; apply he.trans_eq; rw [show t^i=t^(i-n)*t^n from (pow_add t (i-n) n|>.symm.trans (congr_arg _ (Nat.sub_add_cancel hi))).symm]; field_simp
lemma parkF {p:ℕ→F}(n:ℕ)(hp:Thick r p):Thick r (fun i=>p (i+n)):=by obtain ⟨q,hq,hx,c,hC⟩:= hp.Bill; exact Thick.hex ⟨c*q^n, fun i=> (hC _).trans_eq (by rw[pow_add,mul_comm (q^i),mul_assoc])⟩ hq hx
end YM.OPE.Hark
