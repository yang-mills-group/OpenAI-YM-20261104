import YM.Integration.WilsonThermometerWeakProbeScale
import YM.Integration.WilsonThermometerWeakMomentPoint

/-! From signed compact continuum tests at finite external order D to the
point value on a smaller compact set. The scale and the finite derivative
demand may depend on that actual D, even when it grows with the elected order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakValueRecovery
open Set Filter MeasureTheory Spec Function Metric
open WilsonThermometerWeakProbeTest
open scoped Classical Topology BigOperators ContDiff
variable {A E Y:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {n:ℕ}
def Price (l:Filter A)(U:Set E)(F:A→E→Y)(g:A→ℝ)(Q j:ℕ):Prop:=
  ∀K,IsCompact K→K⊆U→∃C,0≤C ∧ ∀ᶠr in l,∀x∈K,‖iteratedFDeriv ℝ j (F r) x‖≤C*g r^Q
def Bounded (l:Filter A)(U:Set E)(F:A→E→Y)(j:ℕ):Prop:=
  ∀K,IsCompact K→K⊆U→∃B,0≤B ∧ ∀ᶠr in l,∀x∈K,‖iteratedFDeriv ℝ j (F r) x‖≤B
def Signed (l:Filter A)(U:Set (Points n))(F:A→Points n→ℂ)(g:A→ℝ)(Q D:ℕ):Prop:=
  ∀K,IsCompact K→K⊆U→∃C,0≤C ∧ ∀ᶠr in l,∀(φ:Test n),tsupport (φ:Points n→ℂ)⊆K→∀w:ℝ,
    0≤w→Charges φ D w→‖φ.applyTo (F r)‖≤C*g r^Q*w

theorem collar {K:Set E}{z y:E}(hz:z∈K){δ R h:ℝ}(pos:0≤h)(norm:‖y‖≤R)(bound:h*R≤δ):
    z+h • y∈cthickening δ K:=by
  apply mem_cthickening_of_dist_le _ z _ _ hz
  rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg pos]
  exact (mul_le_mul_of_nonneg_left norm pos).trans bound

theorem original {l:Filter A}{U:Set (Points n)}(openU:IsOpen U)(clear:U⊆conf n)
    (F:A→Points n→ℂ)(g:A→ℝ)(Q D:ℕ)(limit:Tendsto g l (𝓝 0))(positive:∀ᶠr in l,0<g r)
    (smooth:∀ᶠr in l,ContDiffOn ℝ ∞ (F r) U)
    (signed:Signed l U F g (Q+1) D)(bound:Bounded l U F ((4*n+D+1)*Q+1)):
    Price l U F g Q 0:=by
  intro K compact inside
  rcases K.eq_empty_or_nonempty with rfl|⟨z₀,hz₀⟩
  · exact ⟨0,le_rfl,Eventually.of_forall (by simp)⟩
  let b:=4*n+D;let M:=(b+1)*Q
  obtain ⟨ψ,mass,moments⟩:=WilsonThermometerWeakJointMoments.original M (clear (inside hz₀))
  obtain ⟨w,wp,paid⟩:=charge ψ D
  obtain ⟨R₀,rad⟩:=ψ.hasCompactSupport.isBounded.exists_norm_le
  let R:=max 1 R₀
  have Rp:0<R:=zero_lt_one.trans_le (le_max_left ..)
  have radius:∀y∈tsupport ψ,‖y‖≤R:=fun y hy=>(rad y hy).trans (le_max_right ..)
  obtain ⟨δ,dp,near⟩:=compact.exists_cthickening_subset_open openU inside
  let K':=cthickening δ K
  have compact':IsCompact K':=compact.cthickening
  obtain ⟨C,Cn,asks⟩:=signed K' compact' near
  obtain ⟨B,Bn,jets⟩:=bound K' compact' near
  let W:ℝ:=(∫y,‖ψ y‖)*(B*R^(M+1)/(M.factorial:ℝ))
  have Wn:0≤W:=mul_nonneg (integral_nonneg fun _=>norm_nonneg _) (by positivity)
  refine ⟨C*w+W,add_nonneg (mul_nonneg Cn wp.le) Wn,?_⟩
  let h:=fun r=>WilsonThermometerWeakProbeScale.size b (g r)
  have thin:∀ᶠr in l,h r<δ/R:=(WilsonThermometerWeakProbeScale.shrinks b limit).eventually_lt_const (div_pos dp Rp)
  filter_upwards [positive,limit.eventually_lt_const zero_lt_one,thin,smooth,asks,jets] with r gp small scale sm ask jet x hx
  obtain ⟨hp,hl,testCost,tailCost⟩:=WilsonThermometerWeakProbeScale.original b Q gp small.le
  have moved (y)(hy:y∈tsupport ψ)(t)(ht:t∈Icc (0:ℝ) (h r)):x+t • y∈K':=
    collar hx ht.1 (radius y hy) ((mul_le_mul_of_nonneg_right ht.2 Rp.le).trans ((lt_div_iff₀ Rp).mp scale).le)
  have cased:∀y∈tsupport ψ,x+h r • y∈K':=fun y hy=>moved _ hy _ (right_mem_Icc.mpr hp.le)
  let φ:=probe ψ x hp (fun y hy=>clear (near (cased y hy)))
  have enrolled:=supported ψ x hp cased compact'.isClosed (near.trans clear)
  have read:=ask φ enrolled _ (mul_nonneg (by positivity) wp.le) (priced ψ x hp hl _ paid)
  have test:‖ψ.applyTo (fun y=>F r (x+h r • y))‖≤C*w*(g r)^Q:=by
    rw [tested] at read
    refine read.trans ?_
    calc C*g r^(Q+1)*((h r)⁻¹^b*w) = C*w*(g r^(Q+1)*(h r)⁻¹^b):=by ring
         _≤_:=mul_le_mul_of_nonneg_left testCost (mul_nonneg Cn wp.le)
  have err:=WilsonThermometerWeakMomentPoint.bias ψ mass moments (U:=U) openU (F r) sm x hp
    (fun y hy t ht=>near (moved y hy t ht)) Bn Rp.le radius (fun y hy t ht=>jet _ (moved y hy t ht))
  have error:‖ψ.applyTo (fun y=>F r (x+h r • y))-F r x‖≤W*(g r)^Q:=by
    refine err.trans ?_
    calc (∫y,‖ψ y‖)*(B*R^(M+1)*h r^(M+1)/(M.factorial:ℝ)) = W*(h r)^(M+1):=by dsimp [W];ring
         _≤_:=mul_le_mul_of_nonneg_left tailCost Wn
  rw [norm_iteratedFDeriv_zero]
  calc ‖F r x‖ ≤ ‖F r x-ψ.applyTo (fun y=>F r (x+h r • y))‖+‖ψ.applyTo (fun y=>F r (x+h r • y))‖:=norm_le_norm_sub_add _ _
       _ ≤ W*g r^Q+C*w*g r^Q:=add_le_add ((norm_sub_rev ..).le.trans error) test
       _ = _:=by ring
end YM.Integration.WilsonThermometerWeakValueRecovery
end
