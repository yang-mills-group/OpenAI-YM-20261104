import YM.Integration.WilsonThermometerWeakValueRecovery

/-! Finite derivative recovery on a compact configuration collar. A value
estimate at order 2^j P pays every j-th directional derivative at order P. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakJetRecovery
open Set Filter Function Metric
open WilsonThermometerWeakValueRecovery WilsonThermometerWeakSpatialTaylor
open scoped Classical Topology BigOperators ContDiff
universe u
variable {A:Type*}{E Y:Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem first {l:Filter A}{U:Set E}(openU:IsOpen U)(F:A→E→Y)(g:A→ℝ){P:ℕ}(pp:0<P)
    (limit:Tendsto g l (𝓝 0))(positive:∀ᶠr in l,0<g r)
    (smooth:∀ᶠr in l,ContDiffOn ℝ ∞ (F r) U)(values:Price l U F g (2*P) 0)(curve:Bounded l U F 2):
    Price l U (fun r=>fderiv ℝ (F r)) g P 0:=by
  intro K compact safe
  obtain ⟨δ,dp,sub⟩:=compact.exists_cthickening_subset_open openU safe
  let K':=cthickening δ K
  have compact':IsCompact K':=compact.cthickening
  obtain ⟨C,Cn,upper⟩:=values K' compact' sub
  obtain ⟨B,Bn,der⟩:=curve K' compact' sub
  let h:=fun r=>g r^P
  have decay:Tendsto h l (𝓝 0):=by simpa only [h,zero_pow pp.ne'] using limit.pow P
  refine ⟨2*C+B,by positivity,?_⟩
  filter_upwards [decay.eventually_lt_const dp,positive,smooth,upper,der] with r low gp sm val bound x hx
  have hp:0<h r:=pow_pos gp _
  have member (y:E)(unit:‖y‖=1)(t)(ht:t∈Icc (0:ℝ) (h r)):x+t • y∈K':=
    collar hx ht.1 unit.le (by simpa only [mul_one] using ht.2.trans low.le)
  have loc:x∈K':=Metric.self_subset_cthickening K hx
  have money (v)(hv:v∈K'):‖F r v‖≤C*(h r)^2:=by
    simpa only [norm_iteratedFDeriv_zero,h,←pow_mul,Nat.mul_comm P 2] using val v hv
  rw [norm_iteratedFDeriv_zero]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro y unit
  have invoice:=remainder (F r) openU sm 1 hp (fun t ht=>sub (member y unit t ht))
    (fun t ht=>bound _ (member y unit t ht))
  have poly:polynomial (F r) x (h r) 1 y = F r x+h r • fderiv ℝ (F r) x y:=by
    simp [polynomial,Finset.sum_range_succ,iteratedFDeriv_one_apply]
  rw [poly,unit] at invoice
  simp only [one_pow,mul_one,Nat.factorial_one,Nat.cast_one,div_one] at invoice
  have hy:=money _ (member y unit _ (right_mem_Icc.mpr hp.le))
  have h0:=money x loc
  have triangle:‖h r • fderiv ℝ (F r) x y‖≤2*C*(h r)^2+B*(h r)^2:=by
    calc ‖h r • fderiv ℝ (F r) x y‖ =
          ‖(F r (x+h r • y)-F r x)-(F r (x+h r • y)-(F r x+h r • fderiv ℝ (F r) x y))‖:=by congr 1;abel
         _≤ ‖F r (x+h r • y)‖+‖F r x‖+‖F r (x+h r • y)-(F r x+h r • fderiv ℝ (F r) x y)‖:=
           (norm_sub_le ..).trans (add_le_add (norm_sub_le ..) le_rfl)
         _≤_:=by
           change _≤B*(h r)^2 at invoice
           calc _ ≤ C*(h r)^2+C*(h r)^2+B*(h r)^2:=add_le_add (add_le_add hy h0) invoice
                _ = _:=by ring
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hp] at triangle
  change ‖fderiv ℝ (F r) x y‖≤(2*C+B)*h r
  apply le_of_mul_le_mul_left (a:=(h r)) _ hp
  nlinarith only [triangle]

theorem original {l:Filter A}{U:Set E}(openU:IsOpen U)(F:A→E→Y)(g:A→ℝ)(j P:ℕ)(pp:0<P)
    (limit:Tendsto g l (𝓝 0))(positive:∀ᶠr in l,0<g r)
    (smooth:∀ᶠr in l,ContDiffOn ℝ ∞ (F r) U)(values:Price l U F g (2^j*P) 0)
    (bounds:∀a,2≤a→a≤j+1→Bounded l U F a):Price l U F g P j:=by
  induction j generalizing Y with
  | zero=>simpa using values
  | succ j ih=>
    let V:A→E→(E→L[ℝ]Y):=fun r=>fderiv ℝ (F r)
    have differentiable:∀ᶠr in l,ContDiffOn ℝ ∞ (V r) U:=smooth.mono fun r good x hx=>
      (((good x hx).contDiffAt (openU.mem_nhds hx)).fderiv_right (m:=∞) (by simp)).contDiffWithinAt
    have val:Price l U V g (2^j*P) 0:=first openU F g (by positivity) limit positive smooth
      (by simpa only [pow_succ] using (show Price l U F g (2*(2^j*P)) 0 by convert values using 1;ring))
      (bounds 2 le_rfl (by omega))
    have bounded (a:ℕ)(lo:2≤a)(hi:a≤j+1):Bounded l U V a:=by
      intro K compact sub
      obtain ⟨B,Bn,pay⟩:=bounds (a+1) (by omega) (by omega) K compact sub
      exact ⟨B,Bn,pay.mono fun r yes x hx=>(norm_iteratedFDeriv_fderiv (𝕜:=ℝ) (f:=F r) (x:=x) (n:=a)).le.trans (yes x hx)⟩
    have charged:Price l U V g P j:=ih (Y:=E→L[ℝ]Y) V differentiable val bounded
    intro K compact sub
    obtain ⟨C,Cn,ready⟩:=charged K compact sub
    exact ⟨C,Cn,ready.mono fun r yes x hx=>(norm_iteratedFDeriv_fderiv (𝕜:=ℝ) (f:=F r) (x:=x) (n:=j)).ge.trans (yes x hx)⟩

end YM.Integration.WilsonThermometerWeakJetRecovery
end
