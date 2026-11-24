import YM.OPE.Compatible.Spades.Mass
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
/-! # Probability norm book for angular stabilities. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {X Y:Type}{s t c:ℝ}
open PertExtension Series Libra GaussianScore Jargon
section
variable [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
variable (B: Law X)(μ:Measure X)[μ.IsAddHaarMeasure]
abbrev rentF := ∫ x,B.kern x ∂μ
noncomputable def sand (x:X) :ℝ := (rentF B μ)⁻¹*B.kern x
lemma stamina (x:X): 0≤sand B μ x:=mul_nonneg (inv_nonneg.mpr (spent μ B).le) (Real.exp_pos _).le
noncomputable def quart : Measure X:= μ.withDensity (fun x=>ENNReal.ofReal (sand B μ x))
omit [μ.IsAddHaarMeasure] in
lemma sandy : Measurable (sand B μ):= measurable_const.mul B.continuous_kern.measurable
lemma turnI : Integrable B.kern μ:= by by_contra h; have hx:=spent μ B; rw [integral_undef h] at hx;exact lt_irrefl _ hx
instance : IsProbabilityMeasure (quart B μ):=by
         refine ⟨?_⟩; have hp : Integrable (sand B μ) μ:= (turnI B μ).const_mul _; rw [quart,withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ←ofReal_integral_eq_lintegral_ofReal hp (Eventually.of_forall (stamina B μ))]; unfold sand; rw [integral_const_mul, inv_mul_cancel₀, ENNReal.ofReal_one]; exact (spent μ B).ne'
lemma has_p (p:X→ℝ) : (∫ x,p x ∂quart B μ)=B.average μ p:=by unfold quart Law.average; rw [integral_withDensity_eq_integral_toReal_smul (sandy B μ|>.ennreal_ofReal) (Eventually.of_forall (fun _=>ENNReal.ofReal_lt_top))]; simp_rw [fun x:X=>ENNReal.toReal_ofReal (stamina B μ x),smul_eq_mul,sand,mul_assoc]; rw [integral_const_mul]; rw [mul_comm]; unfold rentF; rw [div_eq_mul_inv]; congr 1; simp_rw [Pi.mul_apply,mul_comm]
lemma Lux (p:Module.Dual ℝ X): B.average μ (fun i=> Real.exp (p i))=Real.exp (B.wick p p/2):=by
         let Y:=B.inverse p; let k:= Real.exp (B.wick p p/2); have hp(x:X): Real.exp (p x)*B.kern x=k*B.kern (x+(-Y)):=by
            unfold k Law.kern; rw [←Real.exp_add,← Real.exp_add, ←sub_eq_add_neg]; apply congr_arg Real.exp; have hP:= B.applies p; change B.P Y=p at hP; rw[B.P.map_sub,LinearMap.sub_apply,(B.P x).map_sub,(B.P Y).map_sub,B.turns x Y,hP]; change _=p Y/2+ _;ring
         unfold Law.average; simp_rw [Pi.mul_apply,hp]; rw [integral_const_mul,integral_add_right_eq_self]; apply mul_div_cancel_right₀; exact (spent μ B).ne'
lemma UpI (p:Module.Dual ℝ X): Integrable (fun x=>Real.exp (p x)) (quart B μ):=by
        by_contra H
        have h':=has_p B μ (fun x=> Real.exp (p x)); rw [integral_undef H,Lux] at h'; exact (Real.exp_pos _).ne' h'.symm
end
end YM.OPE.Cinders
