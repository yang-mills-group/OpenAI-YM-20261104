import YM.RG12.Strike.Hilt
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
/-! # Subtracted charts on radius scales

Strict-vs-resonant annulus test without assuming nonresonances. Nonresonant has
literal power response on continuous lengths; resonance *could* hide a log, ruled out for
specific sums of all equal local attachment diagrams by separate kernel works. Here include
sourcing from exact radial smooth cutoffs (MS not used; no regulators or phases).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
-- homogeneous away from origin. singular exponent sign.
variable {F:R→ℂ}{p:ℤ}
def VectorLaw (F:R→ℂ)(p:ℤ) := ∀ x:R, x≠0 → ∀ t:ℝ,0<t → F (t•x) = (t:ℂ)^(-p)*F x
lemma scaling (L:Cells) : VectorLaw (barrage field L) (2+(L.length:ℤ)):=by
   induction L with
   | nil=>
     intro x he t ht; change (black (t•x))⁻¹=_ *(black x)⁻¹
     have hr : black (t • x)= (t:ℂ)^2*black x:=by unfold black; rw [norm_smul,Real.norm_of_nonneg ht.le,mul_pow,Complex.ofReal_mul,Complex.ofReal_pow]
     rw [hr]; norm_num; field_simp
   | cons i L ih =>
     intro x hx t ht
     let f:=barrage field L;let h:= -(↑L.length+2:ℤ);let c:=(t:ℂ)^h;have hp : t • x ≠ 0:=smul_ne_zero ht.ne' hx
     have he : (fun z:ℝ=> f (palette i (t•x) (t*z))) =ᶠ[𝓝 0] (fun z=> c*f (palette i x z)):=by
        have he : Tendsto (palette i x) (𝓝 (0:ℝ)) (𝓝 x):=by nth_rw 2 [show x=palette i x 0 from (born ..).symm];exact (drawing x i).continuousAt
        filter_upwards [he.eventually_ne hx] with z hz
        rw [show (palette i (t • x) (t * z))= t • palette i x z from by unfold palette; rw [smul_add,smul_smul]]; unfold f; rw [ih _ hz t ht]; dsimp only [c,h]; rw [add_comm] -- order proof
     let A(y:R)(z:ℝ):= f (palette i y z)
     have hh(y:R)(hy:y≠0): DifferentiableAt ℝ (A y) 0:=by
         refine (DifferentiableAt.comp (𝕜:=ℝ) _ ((vellum punct_open punct_field L (palette i y 0) (by rw [born]; exact hy)).differentiableAt (by decide)) (drawing y i).differentiableAt)
     have hj: (t:ℂ) * hit i f (t • x) = c * hit i f x:=by
        have hti: HasDerivAt (fun z:ℝ=> t*z) t 0 := by simpa only [zero_mul,id_eq, mul_one,zero_add] using! (hasDerivAt_const (0:ℝ) t).mul (hasDerivAt_id' 0)
        have ha := (show DifferentiableAt ℝ (A (t • x)) (t*0) from by rw [mul_zero]; exact (hh (t•x) hp)).hasDerivAt.scomp (h:=fun z:ℝ=>t*z) 0 hti -- x wrong use comp or scomp
        have hx := ((hasDerivAt_const (0:ℝ) c).mul (hh x hx).hasDerivAt)
        have hz := (ha.congr_of_eventuallyEq he.symm).unique hx
        rw [Complex.real_smul] at hz
        simpa only [hit,A,mul_zero,zero_mul,zero_add] using! hz
     let k:ℤ:= -(2+(↑(i::L).length:ℤ));have hK:k=h-1:=by unfold k h;simp;ring
     change hit i f (t • x)=(t:ℂ)^k*hit i f x; have hv:(t:ℂ)≠0:=by exact_mod_cast ht.ne'
     apply mul_left_cancel₀ hv; rw [hj,hK,zpow_sub₀ hv,zpow_one]; unfold c; field_simp
lemma escalates (T:Foil)(L D:Cells)(i:Axis4): VectorLaw (leg T L i D) (2+((D.length+L.length+1:ℕ):ℤ)):=by
    intro x hx t ht
    unfold leg tube; simp_rw [scaling _ x hx t ht,List.length_append,List.length_cons,List.length_nil]; rw [mul_sum]; apply sum_congr rfl; intro j _; ring
lemma rays {n:ℕ}{P:Strip n→ℂ}: VectorLaw (fall P) (-(n:ℤ)):=by
    intro x hx t ht
    unfold fall rain; simp only [PiLp.smul_apply, smul_eq_mul,Complex.ofReal_mul, prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,neg_neg,zpow_natCast,mul_sum]; apply sum_congr rfl; intro k _;ring
lemma VectorLaw.mul {F G:R→ℂ}{n m:ℤ}(hF:VectorLaw F n)(hG:VectorLaw G m):VectorLaw (F*G) (n+m):=by
    intro v hv t ht
    have he:(t:ℂ)≠0:=by exact_mod_cast ht.ne'
    change F _*G _= _* (F v*G v)
    rw [hF _ hv _ ht,hG _ hv _ ht,neg_add,zpow_add₀ he]; ring

-- layouts and translations of radial cutoff. 
variable {χ:R→ℂ}
structure Base (χ:R→ℂ) : Prop extends Round χ where
    head : χ=ᶠ[𝓝 0] (fun _=>1)
abbrev logCost (t:ℝ)(x:R):= t • x
-- direction dilation can be positive arbitrary
def bare (χ:R→ℂ)(t:ℝ)(x:R):ℂ:= χ (logCost t x)
def hunt (χ:R→ℂ)(t:ℝ):R→ℂ:=bare χ t-χ
include χ
lemma earns (h:Base χ)(t:ℝ)(ht:t≠0): Round (bare χ t):=by
   let g:R ≃ₜ R:=Homeomorph.smulOfNeZero t ht
   have he(x:R):g x=t • x:=rfl
   refine ⟨⟨h.continu.comp (continuous_const_smul t),?_⟩,fun U x=>?_⟩
   · have hs:= h.compact.comp_homeomorph g;exact hs
   unfold bare logCost; rw [← map_smul, h.iso]
lemma dries (h:Base χ)(t:ℝ)(ht:0 < t):Dried (hunt χ t):=by
   have he:=earns h t ht.ne'
   have hh : Tendsto (logCost t) (𝓝 0) (𝓝 0):=by convert (continuous_const_smul t: Continuous (logCost t)).continuousAt.tendsto (x:=0); first | rfl | simp
   refine ⟨⟨⟨he.continu.sub h.continu,he.compact.sub h.compact⟩,fun L x=>by simp only [hunt,Pi.sub_apply, h.iso,he.iso]⟩,?_⟩
   filter_upwards [hh.eventually h.head,h.head] with i hi hz
   simp only [hunt,Pi.sub_apply,bare,hi,hz,sub_self, Pi.zero_apply]
variable (h: Base χ)
abbrev paid (χ F:R→ℂ)(t:ℝ)(x:R):ℂ:= hunt χ t x * F x
-- one-mark annulus subtraction dependence
def toll (χ F:R→ℂ)(t:ℝ):=∫ x:R,paid χ F t x
include h
lemma achieved (F:R→ℂ)(hf:∀ x:R,x≠0→ContinuousAt F x)(t:ℝ)(ht:0 < t) : Integrable (paid χ F t):=by
   have hw:=withered (dries h t ht) _ hf; exact (hw.continu.integrable_of_hasCompactSupport hw.compact)
lemma price (F:R→ℂ)(hf:∀ x:R,x≠0→ContinuousAt F x){p:ℤ}(hp:VectorLaw F (4+p)) (s t:ℝ)(hs:0 < s)(ht:0 < t):
    toll χ F (s*t)= (t:ℂ)^p*toll χ F s+toll χ F t :=by
   let c := (t:ℂ)^(4+p)
   have ht' : (t:ℂ)≠0:=by exact_mod_cast ht.ne'
   have he(x): paid χ F (s*t) x=c*paid χ F s (t•x)+paid χ F t x:=by
      unfold paid hunt bare logCost; simp only [Pi.sub_apply]; by_cases hf:x=0
      · subst x; simp
      rw [←smul_smul s t x,hp _ hf t ht]
      unfold c; rw [zpow_neg]; field_simp;ring
   unfold toll; simp_rw [he]; rw [integral_add,MeasureTheory.integral_const_mul, MeasureTheory.Measure.integral_comp_smul_of_nonneg (volume) _ t (hR:=ht.le),Complex.real_smul,show Module.finrank ℝ R=4 by simp]
   · push_cast; unfold c;rw [zpow_add₀ ht']; norm_num; field_simp -- maybe ring
   · exact ((achieved h F hf _ hs).comp_smul ht.ne').const_mul c
   exact achieved h F hf t ht
-- no log at *nonresonant* weight independent of Λ. order coincidence Taylor kept separate.
lemma coupon (F:R→ℂ)(hf:∀ x:R,x≠0→ContinuousAt F x){p:ℕ}(hp:VectorLaw F (4+(p:ℤ)))(hx:0 < p):∃ C:ℂ,∀ t:ℝ,0<t → toll χ F t=C*((t:ℂ)^p-1):=by
   let s:ℂ:=(2:ℂ)^p-1; have ht:s≠0:= sub_ne_zero.mpr (by exact_mod_cast (one_lt_pow₀ (by norm_num: (1:ℝ)<2) hx.ne').ne')
   refine ⟨toll χ F 2/s,fun t hv=>?_⟩
   have he := ((price h F hf hp t 2 hv zero_lt_two).symm.trans ((congr_arg (toll χ F) (mul_comm ..)).trans (price h F hf hp 2 t zero_lt_two hv)))
   rw [zpow_natCast,zpow_natCast,Complex.ofReal_ofNat] at he
   field_simp; unfold s; linear_combination he
end YM.RG12.Strike
