import YM.Integration.WilsonPositionScaleLawGuardBarrier

/-! A strict dyadic lower-grade contraction controls every chosen inverse logarithmic power simultaneously across the original field roster. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardContraction
open Function Filter Set
open WilsonPositionScaleLawWholeGrowth (weight)
open scoped Topology Classical Asymptotics

theorem slow (m:ℕ):∀ᶠn:ℕ in atTop,weight m (n+1)≤(5/4)*weight m n:=by
  have factor:Tendsto (fun n:ℕ=>(1+1/((n:ℝ)+1))^m) atTop (𝓝 (1:ℝ)):=by
    simpa only [add_zero,one_pow] using ((tendsto_const_nhds (x:=(1:ℝ))).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))).pow m
  filter_upwards [(tendsto_order.mp factor).2 (5/4) (by norm_num)] with n hn
  let a:ℝ:=(n:ℝ)+1
  have ha:0<a:=by dsimp only [a];positivity
  change ((↑(n+1):ℝ)+1)^m≤(5/4)*a^m
  rw [Nat.cast_add_one]
  have ratio:(1+1/a)*a=a+1:=by field_simp
  calc _=((1+1/a)*a)^m:=congrArg (·^m) ratio.symm
       _=(1+1/a)^m*a^m:=mul_pow .. 
       _≤_:=mul_le_mul_of_nonneg_right hn.le (pow_nonneg ha.le _)

theorem original {I:Type*}(m:ℕ)(v:ℕ→I→ℝ)(C:I→ℝ)(pos:∀n i,0≤v n i)
    (paid:∀ᶠn:ℕ in atTop,∀i:I,3*weight m (n+1)*v (n+1) i≤2*weight m (n+1)*v n i+C i):
    ∃N:ℕ,∀i:I,∃B:ℝ,0≤B ∧ ∀n,N≤n→weight m n*v n i≤B:=by
  let x(n:ℕ)(i:I):=weight m n*v n i
  have stage:∀ᶠn:ℕ in atTop,∀i:I,3*x (n+1) i≤(5/2)*x n i+C i:=by
    filter_upwards [slow m,paid] with n cheap next i
    have cost:=mul_le_mul_of_nonneg_right cheap (pos n i)
    change 3*(weight m (n+1)*v (n+1) i)≤(5/2)*(weight m n*v n i)+C i
    linarith only [next i,cost]
  obtain ⟨N,after⟩:=eventually_atTop.mp stage
  refine ⟨N,?_⟩;intro i
  let B:=max (x N i) (2*C i)
  have base:x N i≤B:=le_max_left ..
  have damping:2*C i≤B:=le_max_right ..
  have hb:0≤B:=(mul_nonneg (zero_le_one.trans (WilsonPositionScaleLawWholeGrowth.positive ..)) (pos N i)).trans base
  refine ⟨B,hb,?_⟩;intro n hn
  obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le hn
  clear hn
  change x (N+j) i≤B
  induction j with
  | zero=>exact base
  | succ j ih=>
    have step:=after (N+j) (Nat.le_add_right ..) i
    change x (N+j+1) i≤B
    linarith only [ih,step,damping]

end YM.Integration.WilsonPositionScaleLawGuardContraction
