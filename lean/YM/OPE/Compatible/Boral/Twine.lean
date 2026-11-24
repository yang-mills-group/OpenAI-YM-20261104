import YM.OPE.Compatible.Boral.Sense
/-! # Pull any probability expenses determined by finite law. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders
variable {X Y:Type}{t s:ℝ}{i:ℕ} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
open Lav
variable (A:Law X)(μ:Measure X)[μ.IsAddHaarMeasure]
local notation "Ψ"=> quart A μ
section
variable [NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y][MeasurableSpace Y][BorelSpace Y]
variable (B:Law Y)(ν:Measure Y)[ν.IsAddHaarMeasure] (g:X→L[ℝ] Y)(h:∀ p:Y→ℝ,a_ (quart A μ) (p∘g)=a_ (quart B ν) p)
include h
lemma quartMap : MeasurePreserving g (quart A μ) (quart B ν):=by
        have hg:= g.continuous.measurable; refine ⟨hg,Measure.ext (fun s hs=>?_)⟩; rw [Measure.map_apply hg hs]; refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_; have he : MeasurableSet (g ⁻¹' s):= hg hs
        have hx:=h (s.indicator (fun _=>1)); rw [show s.indicator (fun (_:Y)=> (1:ℝ)) ∘ g =(g ⁻¹' s).indicator (fun _=>1) from ?_] at hx; unfold a_ at hx; simp only[integral_indicator hs,integral_indicator he,setIntegral_const,smul_eq_mul,mul_one] at hx; exact hx
        funext i; by_cases h:g i ∈ s <;>simp only[Function.comp_apply, indicator_of_notMem,indicator_of_mem, Set.mem_preimage,h,not_false_eq_true]
lemma Reprice {p:Y→ℝ}(hp: Fault (quart B ν) i p t): Fault (quart A μ) i (p ∘ g) t:=by let he:= quartMap A μ B ν g h; exact ⟨hp.pos,hp.strong.comp_measurePreserving he,(eLpNorm_comp_measurePreserving hp.strong he).trans_le hp.passes⟩
end
lemma Stoam {p:X→ℝ}(hp:Bond p) : Pu Ψ p :=by -- close closure via Lal
       induction hp with
       | keep=> exact flipP _
       | glyph p=> intro j hj; let t:=Real.sqrt ‖A.wick p p‖; refine ⟨_, Lal A μ p (Real.sqrt_nonneg _) (le_trans (Real.le_norm_self _) (le_of_eq ((Real.sq_sqrt (norm_nonneg _)).symm))) hj⟩
       | add _ _ H I=> exact addedP H I
       | mul _ _ H I=> exact timesP H I
end YM.OPE.Borealis
