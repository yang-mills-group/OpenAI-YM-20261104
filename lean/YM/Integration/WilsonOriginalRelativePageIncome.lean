import YM.Integration.WilsonOriginalRelativePageTail
import YM.UVNext.PRICED_KERNELS.Basin

/-! Uniform count of the independently chosen physical page assignments using
a connected estimate for each placement. No factor depends on the covering multiplicity. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalRelativePageIncome
open Lattice Finset Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset UVNext.PricedKernels
open WilsonOriginalRelativePageTail
open scoped BigOperators Classical
variable {n N:Side} {ι X:Type*}

private theorem fiber (h:n.val∣N.val) (root z:Site N) {t:ℝ} (pos:0<t):
    (∑u:Fin (Pages n N),Real.exp (-t*separation root (page h (splitter h z) u).val)) ≤ basin t:=by
  calc
    _ = ∑u:↑(parcel (splitter h) (splitter h z)),Real.exp (-t*separation root u.val):=
      Equiv.sum_comp (page h (splitter h z)) _
    _ = ∑u∈parcel (splitter h) (splitter h z),Real.exp (-t*separation root u):=
      sum_coe_sort (parcel (splitter h) (splitter h z)) (fun y:Site N=>Real.exp (-t*separation root y))
    _ ≤ ∑u:Site N,Real.exp (-t*separation root u):=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>(Real.exp_pos _).le)
    _ ≤ _ :=funnel pos root

theorem cost [Fintype ι] (h:n.val∣N.val) (root:Site N) (site:ι→Site N) {t:ℝ} (pos:0<t):
    (∑p:ι→Fin (Pages n N),Real.exp (-t*∑i:ι,(separation root (locate h site p i):ℝ))) ≤
      (basin t)^Fintype.card ι:=by
  let u (i:ι) (j:Fin (Pages n N)):=Real.exp (-t*separation root (page h (splitter h (site i)) j).val)
  calc
    _ = ∑p:ι→Fin (Pages n N),∏i:ι,u i (p i):=by
      apply sum_congr rfl
      intro p _
      rw [mul_sum,Real.exp_sum]
      rfl
    _ = ∏i:ι,∑j,u i j:=(Fintype.prod_sum u).symm
    _ ≤ ∏_i:ι,basin t:=prod_le_prod (fun _ _=>sum_nonneg fun _ _=>(Real.exp_pos _).le)
      (fun i _=>fiber h root (site i) pos)
    _ = _ :=by simp

/-- The input is a per-placement angular salary on the same occupied connected term.
The radial count supplies its joint salary with half the strip. -/
theorem original [Fintype ι] [Fintype X] (h:n.val∣N.val) (root:Site N) (site:ι→Site N)
    (K:(ι→Fin (Pages n N))→X→ℂ) (span:(ι→Fin (Pages n N))→X→ℝ)
    {ρ A:ℝ} (strip:0<ρ) (fee:0 ≤ A) (length:∀p x,0 ≤ span p x)
    (reach:∀p x i,(separation root (locate h site p i):ℝ) ≤ span p x)
    (one:∀p,(∑x,Real.exp (ρ*span p x)*‖K p x‖) ≤ A):
    (∑p,∑x,Real.exp (ρ/2*span p x)*‖K p x‖) ≤ A*(basin (ρ/(2*(Fintype.card ι+1:ℝ))))^Fintype.card ι:=by
  let t:=ρ/(2*(Fintype.card ι+1:ℝ))
  let d (p:ι→Fin (Pages n N)):=∑i:ι,(separation root (locate h site p i):ℝ)
  have tpos:0<t:=by dsimp [t];positivity
  have table:t*(Fintype.card ι+1:ℝ)=ρ/2:=by dsimp [t];field_simp
  have rate (p) (x:X): Real.exp (ρ/2*span p x) ≤ Real.exp (-t*d p)*Real.exp (ρ*span p x):=by
    have radial:d p ≤ (Fintype.card ι:ℝ)*span p x:=by
      simpa only [d,sum_const,card_univ,nsmul_eq_mul] using (sum_le_sum (fun i (_:i∈univ)=>reach p x i))
    have cap:t*d p ≤ (ρ/2)*span p x:=calc
      _ ≤ t*((Fintype.card ι:ℝ)*span p x):=mul_le_mul_of_nonneg_left radial tpos.le
      _ ≤ t*((Fintype.card ι+1:ℝ)*span p x):=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) (length p x)) tpos.le
      _ = _ :=by rw [←mul_assoc,table]
    rw [←Real.exp_add,Real.exp_le_exp]
    linarith only [cap]
  have bill (p): (∑x,Real.exp (ρ/2*span p x)*‖K p x‖) ≤ Real.exp (-t*d p)*A:=calc
    _ ≤ Real.exp (-t*d p)*(∑x,Real.exp (ρ*span p x)*‖K p x‖):=by
      rw [mul_sum]
      apply sum_le_sum
      intro x _
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right (rate p x) (norm_nonneg _)
    _ ≤ _ :=mul_le_mul_of_nonneg_left (one p) (Real.exp_pos _).le
  calc
    _ ≤ ∑p,Real.exp (-t*d p)*A:=sum_le_sum fun p _=>bill p
    _ = A*(∑p,Real.exp (-t*d p)):=by rw [←sum_mul,mul_comm]
    _ ≤ _ :=mul_le_mul_of_nonneg_left (cost h root site tpos) fee

end YM.Integration.WilsonOriginalRelativePageIncome
