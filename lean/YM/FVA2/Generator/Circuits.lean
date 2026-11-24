import YM.FVA2.Generator.Cut
/-!
# Step in the `Shade.measure` analysis: replace the scaled difference by an annulus integral

Spacing taken to zero. `perimeter`: given convergence (`arrived`) and
the pointwise bounds. See `Generator/Port` for the resulting coefficientwise
criterion `Icon`, and near `Generator/Bottom` for how it's applied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Circuits
open Function Filter Set MeasureTheory Real XSpace
open XSpace.Lows XSpace.Mu XSpace.Tide XSpace.Playpen XSpace.Drama XSpace.Sail Lattice Further.FreeCovariance.KP
open scoped Topology ContDiff BigOperators Classical
variable (χ: Shade.Cut)(s:ℝ)(hs:0<s)
def widen (p:ℝ)(x:Cover):= Shade.pace χ (s*p) x-Shade.pace χ p x
abbrev tilt:= RG12.Strike.hunt ( Generator.rcast χ ) s
include hs
private lemma exchange (x: Cover)(p:ℝ)(h:0<p): tilt χ s ( actual p x )= widen χ s p x:= by
    unfold tilt widen RG12.Strike.hunt; rw [Shade.pace,Shade.pace, if_pos h,if_pos (mul_pos hs h) ]; change ( χ (s • actual p x) :ℂ ) -_= _; unfold actual; rw [mul_smul]
omit hs in
private lemma low_cost (b v d m e:ℝ)(hp:0<b)(hv:0<v)(hm:0<m)(hx:0 ≤ d)(hk:m ≤ b*v)(he:e≤ d*(v^4)⁻¹): e ≤ d/m * b * (v^3)⁻¹:= by
    refine he.trans ?_; calc
      _ = d/m * m * (v^3)⁻¹ * v⁻¹:= by field_simp
      _ ≤ d/m * (b*v) * (v^3)⁻¹ * v⁻¹:= by gcongr
      _ = _:= by field_simp
private lemma edges {p:ℝ}(hp:0<p)(x:Cover)(hx:widen χ s p x≠0): min χ.rIn (χ.rIn / s) /2 ≤ p * area x ∧ p*area x ≤ p + max χ.rOut ( χ.rOut / s ):= by
    let u:=actual p x; obtain ⟨hv,hw⟩:= Shade.size_actual hp x; let z:=‖u‖
    have he:= show ‖actual (s*p) x‖=s * z from by rw [actual,mul_smul,norm_smul,Real.norm_of_nonneg hs.le]; rfl
    let r:= min χ.rIn (χ.rIn / s); have h₁:r < z:= lt_of_not_ge (fun hz=> hx (by
       have hp₁ := le_trans hz (min_le_left ..); have hp₂:s*z ≤ χ.rIn:= mul_comm z s ▸ ((le_div_iff₀ hs).mp (hz.trans (min_le_right ..))) -- orientation
       rw [widen, Shade.cut_inside _ _ _ hp hp₁, Shade.cut_inside _ _ _ (mul_pos hs hp) ( he.symm ▸ hp₂ ),sub_self] ))
    have h₂:z < max χ.rOut (χ.rOut/s):= lt_of_not_ge (fun hz=> hx (by
       unfold widen; have hu:= le_trans ( le_max_left .. ) hz; have ht:s*z ≥ χ.rOut:= mul_comm z s ▸ (div_le_iff₀ hs).mp ((le_max_right ..).trans hz)
       rw [show Shade.pace χ (s*p) x=0 from by_contra (fun hi=> not_lt_of_ge (he.symm ▸ ht) ( Shade.tag _ _ _ hi ).2), show Shade.pace χ p x= 0 from by_contra (fun hi=> not_lt_of_ge hu ( Shade.tag _ _ _ hi ).2),sub_self] ))
    change p * ↑(reach x) ≤ z at hv; change z ≤ _ at hw
    unfold area; change r/2≤ _ ∧ _≤ _; constructor <;> nlinarith
variable {ι:Type}{L:Filter ι} [L.IsCountablyGenerated] {a:ι→ℝ}
variable (S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)
variable (p: Cover→ℂ)(r:E4→ℂ)
def arrived (L:Filter ι)(a:ι→ℝ)(p:Cover→ℂ)(r:E4→ℂ)(d:ℕ): Prop:= ∀ x:E4,x≠0→ Tendsto (fun i=> (a i:ℂ)⁻¹^d * p (mark (a i) x)) L (𝓝 (r x))
-- performance on annulus. later use pointwise with kernel convergent Books with cost exponent ≥4.
include S he hs
lemma perimeter {C:ℝ}(hc:0 ≤ C) (pC:∀ x,‖p x‖ ≤ C * (area x ^4)⁻¹)(h:arrived L a p r 4) : Tendsto (fun i=> Shade.measure χ (s*a i) p - Shade.measure χ (a i) p) L (𝓝 (∫ x:E4,tilt χ s x*r x)) := by
    have hx (t:ℝ): Summable (fun x:Cover=> Shade.pace χ t x * p x ):= summable_of_ne_finset_zero (s:=(Shade.outfit χ t).support) (fun x ht=> by rw [ ← Shade.outfit_eq,Finsupp.notMem_support_iff.mp ht, zero_mul])
    let g(i:ι)(x:Cover):= widen χ s (a i) x * p x
    have hh(i:ι): Shade.measure χ (s*a i) p-Shade.measure χ (a i) p = ∑' x:Cover, g i x:= by rw [ Shade.sum_eq, Shade.sum_eq, ← Summable.tsum_sub (hx _) (hx _) ]; exact tsum_congr fun x=> ( sub_mul .. ).symm
    simp_rw [hh]; let B:=1+max χ.rOut (χ.rOut/s); let d:= min χ.rIn (χ.rIn/s) /2; have hd:0<d:= by unfold d; exact half_pos (lt_min χ.rIn_pos (div_pos χ.rIn_pos hs))
    let c:= (2*C)/d
    apply (flight g he ((near_minor (4*B+1)).const_mul (c*64)) _ (close_pay _ B g (by unfold c; positivity) he ?_) ?_).2
    · filter_upwards [he,S.eventually (ge_mem_nhds zero_lt_one)] with i hi h' x hv; have hp:= show widen χ s (a i) x≠0 from (fun hx=> hv (by simp [g,hx])); obtain ⟨h₁,h₂⟩:= edges χ s hs hi x hp
      refine ⟨h₂.trans (add_le_add_left h' _), low_cost (a i) (area x) (2*C) d _ hi (included x) hd (by positivity) h₁ ?_ ⟩ -- order left/right
      unfold g; rw [norm_mul]; calc
        _ ≤ 2*(C*(area x^4)⁻¹):= by
               have ht: ‖widen χ s (a i) x‖≤2:= le_trans (norm_sub_le ..) (by linarith [Shade.pace_le χ (s*a i) x, Shade.pace_le χ (a i) x]); gcongr; apply pC
        _ =_ := by ring
    filter_upwards [almost_all] with x hv; have hk:Continuous (tilt χ s):= (( (Generator.present χ).continu.comp (continuous_const_smul s) ):Continuous (RG12.Strike.bare (Generator.rcast χ) s)).sub (Generator.present χ).continu
    apply ( ( (hk.tendsto x).comp (marks x S he) ).mul (h x hv) ).congr'; filter_upwards [he] with i hi
    rw [Function.comp_apply,exchange χ s hs _ _ hi]; unfold steps g; ring
end YM.FVA2.Generator.Circuits
