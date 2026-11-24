import YM.Integration.WilsonPositionScaleLawPanel

/-! A fixed dyadic sequence whose matrix increments cost K/(n+1)
has a polynomial product bound with an explicit exponent and endpoint ratio. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawIteration
open Function Filter Set Metric
open scoped Topology Classical
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]

def walk (A:ℕ→X→L[ℂ]X)(N:ℕ):ℕ→X→X
  | 0,x=>x
  | k+1,x=>A (N+k) (walk A N k x)

private theorem gain (K x:ℝ)(hx:0<x)(p:ℕ)(large:K≤p):1+K/x≤((x+1)/x)^p:=by
  have rate:0≤1/x:=div_nonneg zero_le_one hx.le
  have one:1+1/x=(x+1)/x:=by field_simp
  calc
    1+K/x≤1+(p:ℝ)*(1/x):=by rw [mul_one_div];gcongr
    _≤(1+1/x)^p:=one_add_mul_le_pow (by linarith) p
    _=((x+1)/x)^p:=congrArg (·^p) one

theorem polynomial (A:ℕ→X→L[ℂ]X)(K:ℝ)
    (price:∀ᶠn:ℕ in atTop,‖A n-ContinuousLinearMap.id ℂ X‖≤K/((n:ℝ)+1)):
    ∃N p:ℕ,K≤p ∧ ∀k:ℕ,∀x:X,‖walk A N k x‖≤
      (((N+k:ℕ):ℝ)+1)^p/((N:ℝ)+1)^p*‖x‖:=by
  obtain ⟨N,after⟩:=eventually_atTop.mp price
  obtain ⟨p,high⟩:=exists_nat_ge K
  refine ⟨N,p,high,?_⟩
  intro k x
  have start:0<(N:ℝ)+1:=by positivity
  induction k with
  | zero=>simp [walk,div_self (pow_ne_zero p start.ne')]
  | succ k ih=>
    let n:=N+k
    let v:=walk A N k x
    let δ:=A n-ContinuousLinearMap.id ℂ X
    let h:ℝ:=(n:ℝ)+1
    have pos:0<h:=by dsimp [h];positivity
    have fee:‖δ‖≤K/h:=after n (Nat.le_add_right ..)
    have split:A n v=v+δ v:=by change _=v+(A n v-v);abel
    have step:‖A n v‖≤(1+K/h)*‖v‖:=by
      rw [split,add_mul,one_mul]
      exact (norm_add_le _ _).trans (add_le_add le_rfl ((δ.le_opNorm _).trans (mul_le_mul_of_nonneg_right fee (norm_nonneg _))))
    change ‖A n v‖≤_
    calc
      _≤((h+1)/h)^p*‖v‖:=step.trans (mul_le_mul_of_nonneg_right (gain K h pos p high) (norm_nonneg _))
      _≤((h+1)/h)^p*(h^p/((N:ℝ)+1)^p*‖x‖):=mul_le_mul_of_nonneg_left ih (pow_nonneg (by positivity) p)
      _=((((N+(k+1):ℕ):ℝ)+1)^p/((N:ℝ)+1)^p)*‖x‖:=by
        have next:((N+(k+1):ℕ):ℝ)+1=h+1:=by dsimp [h,n];push_cast;ring
        rw [next,div_pow];field_simp

variable [CompleteSpace X]

theorem backward (A:ℕ→X→L[ℂ]X)(K:ℝ)(hK:0≤K)
    (price:∀ᶠn:ℕ in atTop,‖A n-ContinuousLinearMap.id ℂ X‖≤K/((n:ℝ)+1)):
    ∃L:ℝ,0≤L ∧ ∀ᶠn:ℕ in atTop,(A n).IsInvertible ∧
      ‖(A n).inverse-ContinuousLinearMap.id ℂ X‖≤L/((n:ℝ)+1):=by
  let I:=ContinuousLinearMap.id ℂ X
  have deep:Tendsto (fun n:ℕ=>(n:ℝ)+1) atTop atTop:=by
    apply ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp (tendsto_add_atTop_nat 1)).congr
    intro n;change ((n+1:ℕ):ℝ)=_;simp
  have arrive:Tendsto A atTop (𝓝 I):=tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero' (.of_forall fun _=>norm_nonneg _) price (deep.const_div_atTop K))
  have unit:I.IsInvertible:=⟨ContinuousLinearEquiv.refl ℂ X,rfl⟩
  have unchanged:I.inverse=I:=ContinuousLinearMap.inverse_equiv (ContinuousLinearEquiv.refl ℂ X)
  obtain ⟨c,U,hu,lip⟩:=(unit.contDiffAt_map_inverse (n:=1)).exists_lipschitzOnWith
  have ui:I∈U:=mem_of_mem_nhds hu
  refine ⟨(c:ℝ)*K,mul_nonneg c.coe_nonneg hK,?_⟩
  have good:∀ᶠa:X→L[ℂ]X in 𝓝 I,IsUnit a:=Units.isOpen.mem_nhds (isUnit_one (M:=X→L[ℂ]X))
  filter_upwards [arrive.eventually hu,arrive.eventually good,price] with n hn hit bound
  have bij:=ContinuousLinearMap.isUnit_iff_bijective.mp hit
  refine ⟨⟨ContinuousLinearEquiv.ofBijective (A n) (LinearMap.ker_eq_bot.mpr bij.1) (LinearMap.range_eq_top.mpr bij.2),rfl⟩,?_⟩
  have inv:=lip.dist_le_mul _ hn _ ui
  rw [dist_eq_norm,dist_eq_norm,unchanged] at inv
  exact inv.trans ((mul_le_mul_of_nonneg_left bound c.coe_nonneg).trans_eq (mul_div_assoc _ _ _).symm)

end YM.Integration.WilsonPositionScaleLawIteration
end
