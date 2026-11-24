import YM.OPE.Compatible.Ocher.Slot
/-! # Real conversions. Watch ∞∈ mass. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {X Y E U:Type*}{s t c:ℝ}{i j k:ℕ}
open PertExtension Series Libra GaussianScore Jargon
section
variable [MeasurableSpace X][NormedAddCommGroup E]{μ:Measure X} {f:X→ E}
lemma spoke (hi:0 < i) (hp:Integrable (fun x=>‖f x‖^i) μ): ENNReal.ofReal (∫ x,‖f x‖^i ∂μ)= eLpNorm f (↑i) μ ^i :=by
          rw [ofReal_integral_eq_lintegral_ofReal hp (Eventually.of_forall (fun x=>pow_nonneg (norm_nonneg _) _)),← ENNReal.coe_natCast,← ENNReal.rpow_natCast, ← NNReal.coe_natCast, eLpNorm_nnreal_pow_eq_lintegral (Nat.cast_ne_zero.mpr hi.ne')]; refine lintegral_congr (fun x=>?_); rw [ENNReal.ofReal_pow (norm_nonneg _),NNReal.coe_natCast, ENNReal.rpow_natCast,enorm_eq_nnnorm]; simp [ENNReal.ofReal]
namespace Fault
lemma ofInt (ht:0≤t)(hi:0 < i) (he:AEStronglyMeasurable f μ)(hf:Integrable (fun x=>‖f x‖^i) μ) (hp:(∫ x,‖f x‖^i ∂μ) ≤ t^i) : Fault μ i f t:=by
         refine ⟨ht,he,(ENNReal.pow_le_pow_left_iff hi.ne').mp ?_⟩; rw [←spoke hi hf,← ENNReal.ofReal_pow ht]; exact ENNReal.ofReal_le_ofReal hp
lemma rose (h:Fault μ i f s)(hi:0 < i): Integrable (fun x=>‖f x‖^i) μ ∧ (∫ x, ‖f x‖^i ∂μ) ≤ s^i:=by
         have hp:= h.rich.integrable_norm_pow hi.ne'; refine ⟨hp,?_⟩; have he:=ENNReal.pow_le_pow_left (n:=i) h.passes; rw [← spoke hi hp,←ENNReal.ofReal_pow h.pos] at he; exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg h.pos _)).1 he
lemma pays [NormedSpace ℝ E] [IsProbabilityMeasure μ](h:Fault μ i f s)(hi:1 ≤ i):‖∫ x,f x ∂μ‖≤ s :=by
         apply (norm_integral_le_integral_norm _).trans; simpa only [pow_one] using ((h.mono hi le_rfl).rose Nat.zero_lt_one).2
lemma scaling [NormedSpace ℝ E] (h:Fault μ i f s)(c:ℝ): Fault μ i (c • f) (‖c‖*s):=by
        refine ⟨mul_nonneg (norm_nonneg _) h.pos, aestronglyMeasurable_const.smul h.strong,?_⟩; rw [eLpNorm_const_smul,ENNReal.ofReal_mul (norm_nonneg _)]; rw [ofReal_norm]; exact mul_le_mul_right h.passes _
end Fault
end
end YM.OPE.Cinders
