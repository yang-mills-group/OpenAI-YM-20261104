import YM.FormalOPE.RG10.GaugeGear.Pulse
/-!
 # General weighted finite-step triangular estimate

 Covers close and long with no repeated scale drift. No requirement that clock tends to ∞
 as raw iteration increases; no applying to close and long with different couplings
 without an explicit reexpression. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.GaugeGear.Budget
open Route Function Finset
open scoped Topology BigOperators Classical
variable {I: Type*}
variable {β k N :ℕ} {p : ℕ → I → ℝ} (S: Finset I) (U : I → Finset I) (C X: ℝ) (α W :ℕ→ℝ) (h:I→ℕ)
variable (J:1 ≤ C) (hx:0 ≤ X) (H:X*0=0) (hp:2 ≤ C)

local notation "N+" => 2*β+6
variable (hw : ∀ i∈Icc k N, 0≤ W i) (hn: W N=1)
variable (hat: ∀ i∈Ico k N, W (i+1) ≤ C^β * W i) (hα : ∀ i∈Ico k N,0 ≤ α i ∧ α i * W (i+1) ≤ W i)
variable (hS: (↑S.card:ℝ)≤ C^2)(hM: (↑(N-k):ℝ) ≤ C^2)
variable (hpre : ∀ a∈S, U a⊆ S) (hh : ∀ a∈S,∀ b∈ U a,h b < h a)
variable (hr : ∀ i∈Ico k N,∀ a∈S,p i a ≤ α i*p (i+1) a + C^β*∑ b∈U a, p (i+1) b) (h0:∀ a∈S,p N a ≤ X)
local notation "E" d=> C^(N+* h d)*X
include hp hx hw hat hn hα hS hM hpre hh hr h0
lemma jump (j:ℕ)(hj: j∈ Icc k N)(x:I)(ht:x∈S) : p j x ≤ W j*((1+(↑(N-j):ℝ))*(C^((2*β+6)*h x)*X)):= by
 obtain he|he:= (mem_Icc.mp hj).2.lt_or_eq
 · have hv: j∈ Ico k N:= mem_Ico.mpr ⟨(mem_Icc.mp hj).1,he⟩; have ha:=hw j hj
   let y:= j+1; have hh' : y∈ Icc k N := mem_Icc.mpr ⟨(mem_Icc.mp hj).1.trans (by dsimp [y]; omega),he⟩; have hw':=hw y hh'
   have hc : 0 ≤ C:= le_trans (by norm_num) hp; have H':1≤C:= le_trans (by norm_num) hp
   have hi (b) (hb:b∈S):= jump y hh' b hb
   let u:=(1+ (↑(N-y):ℝ)); have hu : 0 ≤ u:= by unfold u; positivity
   have hg : u ≤ C^3 := by
      have hz: (↑(N-y):ℝ) ≤ C^2:= le_trans (Nat.cast_le.mpr (Nat.sub_le_sub_left (mem_Icc.mp hh').1 N)) hM
      dsimp only [u]; nlinarith [sq_nonneg (C-1), mul_le_mul_of_nonneg_right hp (sq_nonneg C)]
   let n x:ℕ := (2*β+6)*h x
   let f (x:I):= C^ (n x)*X; have hh0 (b:I):0 ≤ f b:= mul_nonneg (pow_nonneg hc _) hx
   apply (hr _ hv _ ht).trans
   let B := W j * (f x)
   have he0: α j*p y x ≤ W j*(u * f x):= (mul_le_mul_of_nonneg_left (hi x ht) (hα j hv).1).trans (le_trans (le_of_eq (show α j*(W y* _)=(α j*W y)*(u*f x) from (mul_assoc ..).symm)) (mul_le_mul_of_nonneg_right (hα j hv).2 (mul_nonneg hu (hh0 _))))
   suffices hz : C^β*∑ b∈ U x,p y b≤ B by
     apply (add_le_add he0 hz).trans
     unfold B; apply le_of_eq; change _= W j*((1+(↑(N-j):ℝ))* f x); unfold u; rw [show N-j=N-y+1 from by unfold y;omega]; push_cast; ring
   by_cases eq : h x = 0
   · have HE: U x=∅:= Finset.eq_empty_iff_forall_notMem.mpr (fun b h' => Nat.not_lt_zero (h b) (eq ▸ hh x ht b h'))
     rw [HE, Finset.sum_empty, mul_zero]; exact mul_nonneg ha (hh0 x)
   let Bf:= C^ ((2*β+6)*(h x-1)) * X; have hB : 0 ≤ Bf:= by unfold Bf; positivity
   have hl := hat j hv
   have Ht b (H':b∈U x): p y b ≤ C^β*W j*(C^3*Bf):= (hi _ (hpre _ ht H')).trans <| (show W y *_ ≤ _ from mul_le_mul hl (mul_le_mul hg ?_ (hh0 b) (pow_nonneg hc _)) (mul_nonneg hu (hh0 b)) (mul_nonneg (pow_nonneg hc _) ha))
   · have hv : (↑(U x).card:ℝ) ≤ C^2:= le_trans (Nat.cast_le.mpr (Finset.card_le_card (hpre x ht))) hS
     -- inspect ordering subgoals
     calc
       _ ≤ C^β*∑ _∈ U x, (C^β*W j*(C^3*Bf)):= mul_le_mul_of_nonneg_left (sum_le_sum Ht) (pow_nonneg hc _)
       _ ≤ C^β*(C^2* (C^β*W j*(C^3 * Bf))):= by rw [sum_const,nsmul_eq_mul]; gcongr
       _ = W j*((C^5 * C^(2*β)) * Bf):= by rw [Nat.mul_comm 2 β,pow_mul]; ring
       _ ≤ W j*((C^6 * C^(2*β))*Bf):= by gcongr; norm_num
       _ = B:= by
         change _=W j*(C^((2*β+6)*h x)*X)
         nth_rw 1 [show h x=h x-1+1 by omega]; unfold Bf; rw [Nat.mul_add,Nat.mul_one,pow_add C ((2*β+6)*(h x - 1)), pow_add]; ring
   · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_left (2*β+6) (Nat.le_pred_of_lt (hh x ht b H')))) hx
 subst j; rw [hn]; simp only [Nat.sub_self, Nat.cast_zero, add_zero, one_mul]; exact (h0 x ht).trans (le_mul_of_one_le_left hx (one_le_pow₀ (by linarith)))
termination_by N-j
decreasing_by omega
end YM.FormalOPE.RG10.GaugeGear.Budget
