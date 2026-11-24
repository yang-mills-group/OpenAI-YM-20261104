import YM.OPE.Compatible.Ocher.Fault
/-!
# all cost and tail prices. centered gaussian on μ
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {X Y:Type}{s t c:ℝ}{i j k:ℕ}
open PertExtension Series Libra GaussianScore Jargon
section
variable [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
variable (B: Law X)(μ:Measure X)[μ.IsAddHaarMeasure]
local notation "Ψ"=> quart B μ
-- poll Q
abbrev StemUp (f:Module.Dual ℝ X) (x:X):=Real.exp (f x)+Real.exp (-f x)
lemma stem (f:Module.Dual ℝ X) : Integrable (StemUp f) Ψ ∧ (∫ x,StemUp f x ∂Ψ)=2*Real.exp (B.wick f f/2):=by
        have hv:= UpI B μ (-f); refine ⟨(UpI B μ f).add hv,?_⟩; rw [show StemUp f=(fun x=>Real.exp (f x))+(fun x=>Real.exp ((-f) x)) from rfl]; simp only [Pi.add_apply]; rw [integral_add (UpI B μ f) hv, has_p,has_p,Lux,Lux]; unfold Law.wick; simp only[map_neg,LinearMap.neg_apply, neg_neg]; ring
omit [FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X] in
lemma bound_p (f:Module.Dual ℝ X)(x:X):Real.exp ‖f x‖≤StemUp f x:=by
    by_cases h:0 ≤ f x
    · rw[Real.norm_of_nonneg h]; exact le_add_of_nonneg_right (Real.exp_nonneg _)
    rw [Real.norm_of_nonpos (not_le.mp h|>.le)]; exact le_add_of_nonneg_left (Real.exp_nonneg _)
abbrev ampleP (i:ℕ):= max 1 ((i.factorial:ℝ)*(2*Real.exp (1/2)))
lemma enroll (f:Module.Dual ℝ X)(h: B.wick f f ≤1)(hi:0 < i): Fault Ψ i (f:X→ℝ) (ampleP i):=by
          let v(x:X):= StemUp f x; let w:ℝ:= i.factorial; have hw: 0 < w:= Nat.cast_pos.mpr i.factorial_pos
          have hx(x:X): ‖f x‖^i ≤ w*v x:=by rw [mul_comm]; exact ((div_le_iff₀ hw).1 ((Real.pow_div_factorial_le_exp ‖f x‖ (norm_nonneg _) i).trans (bound_p f x)))
          have ht:= f.continuous_of_finiteDimensional; have hp:=((stem B μ f).1.const_mul w); have he:Integrable (fun x=> ‖f x‖^i) Ψ:= hp.mono' ((ht.norm.pow _).aestronglyMeasurable) (Eventually.of_forall (fun i=>by simpa only [Real.norm_of_nonneg (show 0 ≤‖f i‖ ^ _ from pow_nonneg (norm_nonneg _) _)] using! hx i)); refine Fault.ofInt (le_trans zero_le_one (le_max_left ..)) hi ht.aestronglyMeasurable he ((integral_mono he hp hx).trans ?_); rw [integral_const_mul,(stem B μ f).2]; apply le_trans _ (le_self_pow₀ (le_max_left (1:ℝ) _) hi.ne'); exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_monotone (show B.wick f f/2≤1/2 by linarith)) (by norm_num)) hw.le).trans (le_max_right ..) -- Defeq v
lemma Lal (f:Module.Dual ℝ X)(ht:0≤c)(hf:B.wick f f≤c^2)(hp:0 < i): Fault Ψ i (f:X→ℝ) (c*ampleP i):=by
          by_cases h:c=0
          · subst c; rw [zero_mul]; have he:f=0:= Classical.byContradiction fun h=> (not_le.mpr (Jargon.wick_pos B f h)) (by simpa using hf); rw [he,←norm_zero (E:=ℝ)]; exact Fault.constant ..
          have hc:= lt_of_le_of_ne ht (Ne.symm h); let v:= c⁻¹ • f; have hx: B.wick v v ≤ 1:=by unfold Law.wick v; rw [map_smul, LinearMap.smul_apply,f.map_smul]; change _⁻¹ * (_⁻¹ * B.wick f f)≤_; rw [←mul_assoc, ←mul_inv, inv_mul_eq_div,div_le_one (mul_pos hc hc),←sq]; exact hf
          have he: (f:X→ℝ)= c • (v:X→ ℝ):= funext fun x=> by change _= c • (c⁻¹ • (f x)); rw [smul_inv_smul₀ h];
          rw[he]; have H:= (enroll B μ v hx hp).scaling c; rwa [Real.norm_of_nonneg ht] at H
lemma defeat (f:Module.Dual ℝ X)(t:ℝ): (Ψ).real {x:X| t<‖f x‖} ≤ (2*Real.exp (B.wick f f/2))*Real.exp (-t):=by
         let L:= {x:X| t<‖f x‖}; have he:MeasurableSet L := measurableSet_lt measurable_const (f.continuous_of_finiteDimensional.norm.measurable); have hp(x:X): L.indicator (fun _=>Real.exp t) x ≤ StemUp f x:=by
            by_cases h:x∈L
            · rw [indicator_of_mem h]; exact (Real.exp_le_exp.mpr (le_of_lt h)).trans (bound_p f x)
            rw [indicator_of_notMem h]; exact add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
         have hv:= integral_mono ((integrable_const (Real.exp t)).indicator he) (stem B μ f).1 hp; rw [integral_indicator he,setIntegral_const, smul_eq_mul,(stem B μ f).2] at hv;rw [Real.exp_neg,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]; exact hv
end
end YM.OPE.Cinders
