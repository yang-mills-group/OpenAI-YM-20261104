import YM.RG02.Limit.Window

/-!
Numerator test with one marked *complex* mode. No implicit dominated
integration without measurability in both components. Uses a small positive
precision gap on this pointwise parameter setup. No growth rate asserted for
size of any Taylor, any collar-radius uniformity, any continuation in a
coarse field or a tag-dependent slice; tariffs are pointwise.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Therm
open Filter Function MeasureTheory Set Metric
open PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Asym
open PowerSeries
open scoped ContDiff Topology Classical Real
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
variable (μ : Measure E)[μ.HasTemperateGrowth]

def beam (K:E→ℂ)(f:E→ℝ)(t:ℝ)(u:E) := K (t • u) * Complex.ofReal (Real.exp (-f (t • u) / t^2))
lemma colors (K:E→ℂ)(f:E→ℝ)(t:ℝ)(u:E) : beam K f t u= ↑(projection (Complex.re ∘ K) f t u) + Complex.I * ↑(projection (Complex.im ∘ K) f t u) := by
   rw [beam, projection_eq,projection_eq]
   simp only [Complex.ofReal_mul,comp_apply]
   rw [← mul_assoc Complex.I,mul_comm Complex.I,←add_mul, Complex.re_add_im]

/-- Both components polynomially integrable and equal to a purely finite
jet expression, including Taylor expansion of the Haar weight as put into K,f. -/
theorem traction {f:E→ℝ}(H : Stationary f)
    (hg : ∃ c>0,∀ u:E,c*‖u‖^2≤jet f 2 u)(hf : Measurable f){K:E→ℂ}(hk : ContDiffAt ℝ ∞ K 0)(hm : Measurable K) :
    ∃ r>0,∀ S : ℝ→Set E, Collars r S → (∀ n, Integrable (visibly f K n) μ) ∧
      (∀ᶠ t in Tested.germ, IntegrableOn (beam K f t) (S t) μ) ∧
      Near (fun t=>∫ u in S t, beam K f t u ∂μ) (PowerSeries.mk fun n=>∫ u, visibly f K n u ∂μ) := by
   let U:= Complex.re ∘ K; let V := Complex.im ∘ K
   have hu : ContDiffAt ℝ ∞ U 0 := Complex.reCLM.contDiff.contDiffAt.comp 0 hk
   have hv : ContDiffAt ℝ ∞ V 0 := Complex.imCLM.contDiff.contDiffAt.comp 0 hk
   have hM : Measurable U := Complex.continuous_re.measurable.comp hm
   have hW : Measurable V := Complex.continuous_im.measurable.comp hm
   obtain ⟨r,hr,hU⟩ := holds H hu.continuousAt hg
   obtain ⟨s,hs,hV⟩ := holds H hv.continuousAt hg
   refine ⟨min r s,lt_min hr hs,fun S he => ?_⟩
   let a : ℕ→ E→ℂ := fun n i=>Complex.ofReal (normTerm U f n i)
   let b : ℕ→ E→ℂ := fun n i=> Complex.I * Complex.ofReal (normTerm V f n i)
   have hA (n) : Integrable (a n) μ := (H.integrableTerm μ hu hg).ofReal
   have hB (n) : Integrable (b n) μ := ((H.integrableTerm μ hv hg).ofReal).const_mul _
   have h' (n) : visibly f K n=a n+b n := funext fun i=>seen hk H i n
   let u : ℝ→E→ℂ := fun t x=> ↑(projection U f t x); let v : ℝ→E→ℂ := fun t x=> Complex.I * ↑(projection V f t x)
   have hX : ∀ᶠ t in Tested.germ,IntegrableOn (u t) (S t) μ ∧ IntegrableOn (v t) (S t) μ := by
      obtain ⟨B,h1,h2,h⟩ := he
      filter_upwards [h,Tested.eventually_pos] with t ht hT
      exact ⟨(pays μ hU hf hM hT|>.mono_set (ht.2.2.trans (preimage_mono (ball_subset_ball (min_le_left ..)))) |>.ofReal),
       (((pays μ hV hf hW hT|>.mono_set (ht.2.2.trans (preimage_mono (ball_subset_ball (min_le_right ..))))).ofReal).const_mul _)⟩
   have hh (t) : beam K f t = u t + v t := funext fun x => colors ..
   refine ⟨fun n => h' n ▸ ((hA n).add (hB n)), hX.mono (fun t ht=>hh t ▸ ht.1.add ht.2),?_⟩
   have hq (n) : ∫ u, visibly f K n u ∂μ = ↑(moment μ U f n) + Complex.I*↑(moment μ V f n) := by
      rw [h',integral_add' (hA n) (hB n)]
      unfold a b moment; rw [integral_const_mul]; exact congr_arg₂ (· + ·) (integral_ofReal (f:= normTerm U f n)) (congr_arg (Complex.I * ·) (integral_ofReal (f:=normTerm V f n)))
   unfold Near; simp_rw [PowerSeries.coeff_mk,hq]
   let P := fun t=>∫ x in S t, projection U f t x ∂μ
   let Q := fun t=>∫ x in S t, projection V f t x ∂μ
   apply Asym.agreement ((convert_x (runway (μ:=μ) H hg hf hu hM hU (he.raise (min_le_left ..)))).add
       (scalar_mul_lift (convert_x (runway (μ:=μ) H hg hf hv hW hV (he.raise (min_le_right ..)))) Complex.I))
   filter_upwards [hX] with t ht
   rw [hh, integral_add' ht.1 ht.2]
   unfold u v; rw [integral_const_mul]
   change ↑(P t)+Complex.I*↑(Q t)=_
   exact congr_arg₂ (·+·) (integral_ofReal (f:=projection U f t)).symm (congr_arg (Complex.I * ·) (integral_ofReal (f:=projection V f t)).symm)

end YM.RG02.Therm
