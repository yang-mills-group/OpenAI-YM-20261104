import YM.MSbar.Sat.Pitch
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Matrix Filter Function Set Metric Finset
open scoped Topology ContDiff BigOperators Classical
variable {n : Side} {ι τ : Type} [Fintype ι] [Fintype τ] [DecidableEq τ]{a C r D ρ m R X T: ℝ}{N K : ℕ}
    {l : ι ⊕ τ → Site n}{f : Positions (ι⊕τ) → ℝ}(H: Receipt l a N K C r m f)
local notation "I"=> Positions (ι⊕τ)
set_option quotPrecheck false
local notation "jW"=> (K:ℝ)*countCost a
variable (k:ℕ)(i:τ)
local notation "q"=> plank f i
local notation "L"=>((l ∘ (Sum.inr:τ→ι⊕τ)))
def prime (l:ι⊕τ→Site n)(k:ℕ)(f:Positions (ι⊕τ)→ℝ)(i:τ):Positions τ:= fun j=> if separation (l (.inr i)) (l (.inr j)) ≤ k then plank f i j else 0
local notation "p!"=> prime l k f i
include H
lemma squareI : Sealed (l ∘(Sum.inr:τ→ι⊕τ)) (tiltWidth K (m/2) a C) (block f 0)⁻¹ ((m/2/2)⁻¹):= (H.priced_inverse (0:I) (mem_closedBall_self H.reserveH_pos.le)).2.1
def ice (K:ℕ)(m a C:ℝ):=(m/2/2)⁻¹*((K:ℝ)*countCost (tiltWidth K (m/2) a C /2))
local notation "a!"=> tiltWidth K (m/2) a C/2
lemma arid : 0 < a! := half_pos (tiltWidth_pos K (half_pos H.pos_m) H.pos_a H.pos_C.le)
lemma income : wash q ≤ ice K m a C :=by
   have he:=squareI H; have hC:0≤ (m/2/2)⁻¹:=by have ht:=H.pos_m; positivity
   unfold ice wash; let A:=l (.inr i)
   have hh(j): |q j|≤ (m/2/2)⁻¹ * Decay a! A (l (.inr j)):=by
       apply le_trans (he i j); apply mul_le_mul_of_nonneg_left _ hC; apply Real.exp_monotone; let B:= l (.inr j); change -(tiltWidth K _ a C)*separation A B≤ (-a!)*(separation A B); gcongr; linarith only [arid H]
   refine le_trans (Finset.sum_le_sum fun j _=> hh j) ?_; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left ((H.mult.comp Sum.inr_injective).count L (arid H) A) hC
lemma salary : wash p! ≤ ice K m a C:=by
   apply le_trans _ (income H i); unfold wash; refine Finset.sum_le_sum fun j _=> ?_; unfold prime; split; exact le_rfl; rw [abs_zero]; exact abs_nonneg _
lemma excess : wash (q-p!) ≤ Real.exp (-a! * k)* ice K m a C := by
   have he:=squareI H; have hC:0≤ (m/2/2)⁻¹:=by have ht:=H.pos_m; positivity
   let A:=L i; let t:= Real.exp (-a!*k)
   have ha:0<a!:= arid H; have hv(j:τ): |(q-p!) j| ≤ t*((m/2/2)⁻¹ * Decay a! A (L j)):=by
       rw [Pi.sub_apply]; unfold prime; split
       next hz=> rw [sub_self,abs_zero]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hC (Real.exp_pos _).le)
       next hz=>
         rw [sub_zero]; apply le_trans (he i j); rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ hC; unfold t Decay; rw [← Real.exp_add]; apply Real.exp_monotone
         have hp:k ≤ separation A (L j) := le_of_not_ge hz; have ht := mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.2 hp) ha.le; change -(tiltWidth ..)*separation A (L j) ≤ _; linarith only [ht] -- notation
   unfold wash; refine le_trans (Finset.sum_le_sum fun j _=> hv j) ?_; rw [← Finset.mul_sum,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((H.mult.comp Sum.inr_injective).count L ha A) hC) (Real.exp_pos _).le
end YM.Push.Uniform
