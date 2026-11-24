import YM.Integration.WilsonPositionScaleLawWholeGrowth

/-! Dyadic power envelope for the whole measured graded norm. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardBarrier
open Filter
open WilsonPositionScaleLawWholeGrowth (weight)
open scoped Topology Classical

theorem gain {K:ℝ}{p:ℕ}(high:K≤p)(n:ℕ):(1+K/((n:ℝ)+1))*weight p n≤weight p (n+1):=by
  let x:ℝ:=(n:ℝ)+1
  have hx:0<x:=by dsimp [x];positivity
  have e:1+1/x=(x+1)/x:=by field_simp
  have step:1+K/x≤((x+1)/x)^p:=calc
    _≤1+(p:ℝ)*(1/x):=by rw [mul_one_div];gcongr
    _≤(1+1/x)^p:=one_add_mul_le_pow (by linarith [one_div_pos.mpr hx]) p
    _=((x+1)/x)^p:=congrArg (·^p) e
  change (1+K/x)*x^p≤_
  calc _≤((x+1)/x)^p*x^p:=mul_le_mul_of_nonneg_right step (pow_nonneg hx.le _)
       _=(x+1)^p:=by rw [div_pow,div_mul_cancel₀ _ (pow_ne_zero _ hx.ne')]
       _=_:=by simp only [weight,x,Nat.cast_add_one]

theorem original {I:Type*}(v:ℕ→I→ℝ){K:ℝ}(hk:0≤K)(pos:∀n i,0≤v n i)
    (fee:∀ᶠn:ℕ in atTop,∀i:I,v (n+1) i≤(1+K/((n:ℝ)+1))*v n i):
    ∃N p:ℕ,∀n,N≤n→∀i:I,v n i≤weight p n*v N i:=by
  obtain ⟨N,after⟩:=eventually_atTop.mp fee
  obtain ⟨p,high⟩:=exists_nat_ge K
  refine ⟨N,p,?_⟩;intro n hn i
  obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le hn
  clear hn
  induction j with
  | zero=>simp only [Nat.add_zero];exact le_mul_of_one_le_left (pos _ _) (WilsonPositionScaleLawWholeGrowth.positive ..)
  | succ j ih=>
    let n:=N+j
    have factor:0≤1+K/((n:ℝ)+1):=by positivity
    change v (n+1) i≤weight p (n+1)*v N i
    calc
      _≤(1+K/((n:ℝ)+1))*v n i:=after n (Nat.le_add_right ..) i
      _≤(1+K/((n:ℝ)+1))*(weight p n*v N i):=mul_le_mul_of_nonneg_left ih factor
      _=((1+K/((n:ℝ)+1))*weight p n)*v N i:=(mul_assoc ..).symm
      _≤_:=mul_le_mul_of_nonneg_right (gain high n) (pos _ _)

end YM.Integration.WilsonPositionScaleLawGuardBarrier
