import YM.Integration.WilsonThermometerWeakJetRecovery
import YM.Integration.WilsonThermometerWeakFiniteDirections

/-! At a fixed high spatial Taylor order an actual signed compact test loses
only one power of the freely chosen displacement scale per derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakSharpPositions
open Set Filter Metric Spec WilsonThermometerWeakValueRecovery
open scoped BigOperators Topology Classical ContDiff
universe u
variable {A:Type*}{E Y:Type u}[NormedAddCommGroup E][NormedSpace ℝ E][ProperSpace E]
    [NormedAddCommGroup Y][NormedSpace ℝ Y]

private theorem first {l:Filter A}{U:Set E}(openU:IsOpen U)(F:A→E→Y)(g:A→ℝ)(P:ℕ)
    (limit:Tendsto g l (𝓝 0))(positive:∀ᶠr in l,0<g r)
    (smooth:∀ᶠr in l,ContDiffOn ℝ ∞ (F r) U)(values:Price l U F g (P+1) 0)(curve:Bounded l U F (P+2)):
    Price l U (fun r=>fderiv ℝ (F r)) g P 0:=by
  intro K compact safe
  obtain ⟨δ,dp,sub⟩:=compact.exists_cthickening_subset_open openU safe
  let K':=cthickening δ K
  have compact':IsCompact K':=compact.cthickening
  obtain ⟨C,Cn,upper⟩:=values K' compact' sub
  obtain ⟨B,Bn,der⟩:=curve K' compact' sub
  obtain ⟨w,select⟩:=WilsonThermometerWeakFiniteDirections.weights P
  let mesh:ℝ:=(P:ℝ)+2
  let stock:ℝ:=∑i,|w i|
  have sn:0≤stock:=Finset.sum_nonneg fun _ _=>abs_nonneg _
  have mn:0≤mesh:=by dsimp [mesh];positivity
  let cash:=stock*(C+B*mesh^(P+2))
  have cn:0≤cash:=mul_nonneg sn (add_nonneg Cn (mul_nonneg Bn (pow_nonneg mn _)))
  have tiny:Tendsto (fun r=>g r*mesh) l (𝓝 0):=by simpa using limit.mul_const mesh
  refine ⟨cash,cn,?_⟩
  filter_upwards [tiny.eventually_lt_const dp,limit.eventually_lt_const zero_lt_one,positive,smooth,upper,der]
    with r collarFee small gp regular amount filed x hx
  rw [norm_iteratedFDeriv_zero]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg cn (pow_nonneg gp.le _))
  intro y yu
  have member (t:ℝ)(ht:t∈Icc (0:ℝ) (g r*mesh)):x+t • y∈K':=
    collar hx ht.1 yu.le (by simpa only [mul_one] using ht.2.trans collarFee.le)
  have charge (i:Fin (P+2)):‖F r (x+(g r*WilsonThermometerWeakFiniteDirections.node i) • y)‖≤C*g r^(P+1):=by
    have pos:0≤WilsonThermometerWeakFiniteDirections.node i:=by dsimp [WilsonThermometerWeakFiniteDirections.node];positivity
    have paid:WilsonThermometerWeakFiniteDirections.node i≤mesh:=by
      dsimp [WilsonThermometerWeakFiniteDirections.node,mesh]
      exact_mod_cast (show i.val+1≤P+2 from i.isLt)
    simpa only [norm_iteratedFDeriv_zero] using amount _ (member _
      ⟨mul_nonneg gp.le pos,mul_le_mul_of_nonneg_left paid gp.le⟩)
  have held:=WilsonThermometerWeakFiniteDirections.bound P w select (F r) openU regular yu gp Bn
    (fun t ht=>sub (member t ht)) (fun t ht=>filed _ (member t ht)) charge
  have reduce:g r^(P+2)≤g r^(P+1):=by
    rw [show P+2=P+1+1 from rfl,pow_succ (g r) (P+1)]
    exact mul_le_of_le_one_right (pow_nonneg gp.le _) small.le
  have scale:(g r*mesh)^(P+2)≤g r^(P+1)*mesh^(P+2):=by
    rw [mul_pow];exact mul_le_mul_of_nonneg_right reduce (pow_nonneg mn _)
  apply le_of_mul_le_mul_left (a:=g r) _ gp
  calc g r*‖(fderiv ℝ (F r) x) y‖≤stock*(C*g r^(P+1)+B*(g r*mesh)^(P+2)):=held
       _≤stock*(C*g r^(P+1)+B*(g r^(P+1)*mesh^(P+2))):=by gcongr
       _=g r*(cash*g r^P):=by dsimp [cash];rw [pow_succ (g r) P];ring

theorem derivatives {l:Filter A}{U:Set E}(openU:IsOpen U)(F:A→E→Y)(g:A→ℝ)(j P:ℕ)
    (limit:Tendsto g l (𝓝 0))(positive:∀ᶠr in l,0<g r)
    (smooth:∀ᶠr in l,ContDiffOn ℝ ∞ (F r) U)(values:Price l U F g (P+j) 0)
    (curve:Bounded l U F (P+j+1)):Price l U F g P j:=by
  induction j generalizing Y with
  | zero=>simpa using values
  | succ j ih=>
    let V:A→E→(E→L[ℝ]Y):=fun r=>fderiv ℝ (F r)
    have differentiable:∀ᶠr in l,ContDiffOn ℝ ∞ (V r) U:=smooth.mono fun r good x hx=>
      (((good x hx).contDiffAt (openU.mem_nhds hx)).fderiv_right (m:=∞) (by simp)).contDiffWithinAt
    have val:Price l U V g (P+j) 0:=first openU F g (P+j) limit positive smooth
      (by simpa only [Nat.add_assoc] using values) (by simpa only [Nat.add_assoc] using curve)
    have budget:Bounded l U V (P+j+1):=by
      intro K compact sub
      obtain ⟨B,Bn,pay⟩:=curve K compact sub
      exact ⟨B,Bn,pay.mono fun r yes x hx=>
        (norm_iteratedFDeriv_fderiv (𝕜:=ℝ) (f:=F r) (x:=x) (n:=P+j+1)).le.trans (yes x hx)⟩
    have lower:=ih (Y:=E→L[ℝ]Y) V differentiable val budget
    intro K compact sub
    obtain ⟨q,qn,pay⟩:=lower K compact sub
    exact ⟨q,qn,pay.mono fun r ready x hx=>
      (norm_iteratedFDeriv_fderiv (𝕜:=ℝ) (f:=F r) (x:=x) (n:=j)).ge.trans (ready x hx)⟩

variable {n:ℕ}
theorem original {l:Filter A}{U:Set (Points n)}(openU:IsOpen U)(clear:U⊆conf n)
    (F:A→Points n→ℂ)(g:A→ℝ)(P j D:ℕ)
    (limit:Tendsto g l (𝓝 0))(positive:∀ᶠr in l,0<g r)
    (smooth:∀ᶠr in l,ContDiffOn ℝ ∞ (F r) U)(signed:WilsonThermometerWeakValueRecovery.Signed l U F g (P+j+1) D)
    (paid:Bounded l U F ((4*n+D+1)*(P+j)+1))(curve:Bounded l U F (P+j+1)):
    Price l U F g P j:=
  derivatives openU F g j P limit positive smooth
    (WilsonThermometerWeakValueRecovery.original openU clear F g (P+j) D limit positive smooth signed paid) curve

end YM.Integration.WilsonThermometerWeakSharpPositions
end
