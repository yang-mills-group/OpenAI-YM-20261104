import YM.Integration.WilsonIndependentSpoutOrbitLedger

/-! A worst allowed placement on each actual board buys every visit before the finite weighted sum. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutVisitWallet
open Finset
open scoped BigOperators Classical
variable {T W:Type}[Fintype T]{B:W → Type}[∀w,Fintype (B w)][∀w,Nonempty (B w)]
theorem original (width tail:W → ℝ)(one:∀w,1≤width w)(positive:∀w,0≤tail w)
    (X Y:(w:W) → B w → T → ℂ)
    (paid:∀(t:T)(pick:∀w,B w),∃k:ℕ,∃H:ℝ,0≤H ∧ ∀w,‖X w (pick w) t-Y w (pick w) t‖≤H*(width w)^k*tail w):
    ∃k:ℕ,∃H:ℝ,0≤H ∧ ∀(w:W)(b:B w)(t:T),‖X w b t-Y w b t‖≤H*(width w)^k*tail w:=by
  have best (t:T)(w:W):∃b:B w,∀c:B w,‖X w c t-Y w c t‖≤‖X w b t-Y w b t‖:=by
    obtain ⟨b,_,hb⟩:=exists_max_image (univ:Finset (B w)) (fun c=>‖X w c t-Y w c t‖) univ_nonempty
    exact ⟨b,fun c=>hb c (mem_univ _)⟩
  choose pick selected using best
  choose k H nonnegative bill using fun t=>paid t (pick t)
  refine ⟨∑i,k i,∑i,H i,Finset.sum_nonneg (fun i _=>nonnegative i),?_⟩
  intro w b t
  refine (selected t w b).trans ((bill t w).trans (mul_le_mul_of_nonneg_right ?_ (positive w)))
  exact mul_le_mul (single_le_sum (fun j _=>nonnegative j) (mem_univ t))
    (pow_le_pow_right₀ (one w) (single_le_sum (fun j _=>Nat.zero_le (k j)) (mem_univ t)))
    (pow_nonneg (zero_le_one.trans (one w)) _) (Finset.sum_nonneg (fun i _=>nonnegative i))

theorem applied {L:Type}[Fintype L](H:ℝ)(X Y:L → ℂ)(pay:∀i,‖X i-Y i‖≤H)(weight:L → ℂ):
    ‖(∑i,weight i*X i)-(∑i,weight i*Y i)‖≤(∑i,‖weight i‖)*H:=by
  rw [←Finset.sum_sub_distrib,Finset.sum_mul]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro i _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (pay i) (norm_nonneg _)

end YM.Integration.WilsonIndependentSpoutVisitWallet
