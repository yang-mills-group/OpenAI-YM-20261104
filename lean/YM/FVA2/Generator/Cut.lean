import YM.FVA2.Scale.System
import YM.RG12.Strike.FirstPulse
/-!
# First-order check.b (toward qgau) — annulus independence

Use the X-space `Photo` calculation on this very prescription. Without using any
rotational symmetry property of our `χ`, the *resonant* moment of weight -4 agrees
exactly with that at a genuine round cutoff. Even after derivatives have
been charged into the kernel, by the same criterion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator
open Function Filter Finset Set MeasureTheory Real RG12.Strike XSpace
open scoped Topology BigOperators Classical
abbrev rcast (χ: Shade.Cut)(x:E4): ℂ:= ↑(χ x)
def round0 (x:E4) : ℂ:= ↑(Real.smoothTransition (2-‖x‖))
lemma roundS : Base round0:= by
    refine ⟨⟨⟨ ?_,?_ ⟩, fun U x=>?_⟩, ?_ ⟩
    · exact continuous_ofReal0.comp (smoothTransition.continuous.comp (continuous_const.sub continuous_norm) )
    · refine HasCompactSupport.intro (K:=Metric.closedBall (0:E4) 2) (isCompact_closedBall ..) (fun x h=> ?_ )
      have hp:= lt_of_not_ge (show ¬ ‖x‖≤ (2:ℝ) from fun he=> h (mem_closedBall_zero_iff.mpr he))
      unfold round0; rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2-‖x‖≤0),Complex.ofReal_zero]
    · unfold round0; rw [LinearIsometryEquiv.norm_map]
    filter_upwards [Metric.closedBall_mem_nhds (0:E4) zero_lt_one] with x hx; unfold round0; rw [Real.smoothTransition.one_of_one_le (by obtain h:=mem_closedBall_zero_iff.mp hx; linarith : 1≤ 2-‖x‖),Complex.ofReal_one]
where continuous_ofReal0 : Continuous (fun x:ℝ=> (x:ℂ)):=Complex.continuous_ofReal
variable (χ:Shade.Cut)
lemma near : rcast χ =ᶠ[𝓝 0] 1:= by
    filter_upwards [Metric.closedBall_mem_nhds (0:E4) χ.rIn_pos] with i hi; simp [rcast, χ.one_of_mem_closedBall hi]
lemma present : Annular (rcast χ):= ⟨ Complex.continuous_ofReal.comp χ.continuous, χ.hasCompactSupport.comp_left (show (↑(0:ℝ):ℂ)=0 from Complex.ofReal_zero) ⟩
variable {f g:E4→ℂ} (h:Annular f)
include h in
lemma stay (p:f=ᶠ[𝓝 0] 0) (hf:∀ x≠0, ContinuousAt g x): Integrable (f*g):= by
   apply Continuous.integrable_of_hasCompactSupport _ h.compact.mul_right; apply continuous_iff_continuousAt.mpr; intro x; by_cases he:x=0
   · subst x; have hv : (f*g)=ᶠ[𝓝 0] (fun _=>0):= p.mono (fun x hx=> (congr_arg (fun k=> k*g x) (show f x=0 from hx)).trans (zero_mul _) ); exact continuousAt_const.congr hv.symm
   exact h.continu.continuousAt.mul ( hf x he )
variable (t:ℝ)(ht:0<t)
include ht
lemma rests (hf:∀ x≠0, ContinuousAt g x): Integrable ( paid (rcast χ) g t):= by
   obtain ⟨hc,hp⟩:= present χ; let U:=(Homeomorph.smulOfNeZero (α:=E4) t ht.ne') -- M?
   apply stay (f:=hunt (rcast χ) t) (g:=g) (Annular.mk ( ((hc.comp ( show Continuous (logCost t) from continuous_const_smul t )): Continuous (bare (rcast χ) t)).sub hc ) ( ( show HasCompactSupport (bare (rcast χ) t) from hp.comp_homeomorph U ).sub hp ) ) _ hf
   have he : Tendsto (fun x:R=> t • x) (𝓝 0) (𝓝 0):= by convert ((continuous_const_smul t: Continuous (logCost t)).continuousAt.tendsto (x:=0)); first | rfl | simp
   filter_upwards [he.eventually (near χ),near χ] with i hi hh; change rcast χ ( t • i )-rcast χ i=0; rw [show rcast χ (t•i)=1 from hi,show rcast χ i=1 from hh, sub_self]
lemma exchange {g:E4→ℂ}(hf:∀ x≠0,ContinuousAt g x)(H:VectorLaw g 4): toll (rcast χ) g t=toll round0 g t:= by
   let f:=( rcast χ - round0 ); obtain hp:= ( present χ ); obtain hR:= roundS.toRound; have he : Annular f:= ⟨hp.continu.sub hR.continu,hp.compact.sub hR.compact⟩; have hh : f=ᶠ[𝓝 0]0:= Filter.EventuallyEq.trans ( ( near χ ).sub ( show round0=ᶠ[𝓝 0] 1 from roundS.head ) ) ( by rw [sub_self] )
   let φ:= f*g; let c:ℂ:= (↑t:ℂ)^4; have hv := stay he hh hf; have hz(x:E4): paid (rcast χ) g t x - paid round0 g t x = c*φ (t•x)-φ x:= by
      by_cases hi:x=0
      · subst x; have hu:=hh.eq_of_nhds; unfold paid hunt bare φ; simp only [Pi.sub_apply, Pi.mul_apply,smul_zero,sub_self, logCost, show f 0=0 from hu, mul_zero,zero_mul]
      unfold paid hunt bare logCost φ; simp only [Pi.sub_apply, Pi.mul_apply]; rw [H x hi t ht]; have hv' : (↑t:ℂ)≠0:=by exact_mod_cast ht.ne'
      unfold f c; dsimp only [Pi.sub_apply]; norm_num [zpow_neg]; field_simp; ring
   unfold toll; apply sub_eq_zero.mp; rw [ ← integral_sub ( rests χ t ht hf ) ( achieved roundS g hf _ ht ) ]; simp_rw [hz]; rw [ integral_sub ( ( hv.comp_smul ht.ne' ).const_mul c ) hv,integral_const_mul,Measure.integral_comp_smul_of_nonneg (volume) φ t (hR:=ht.le),Complex.real_smul,show Module.finrank ℝ R=4 by simp]; have hv' : (↑t:ℂ)≠0:=by exact_mod_cast ht.ne'
   unfold c φ; push_cast; field_simp [ hv' ] ; ring
end YM.FVA2.Generator
