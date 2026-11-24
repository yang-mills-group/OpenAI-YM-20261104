import YM.OPE.Compatible.Roan.Hope
import YM.OPE.Compatible.Sward.Cap
/-! # Budget Pu for smooth invoices. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Spells
variable {X Y:Type}{t s:ℝ}{i:ℕ} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
open Lav Flock
variable (A:Law X)(μ:Measure X)[μ.IsAddHaarMeasure]
local notation "Ψ"=> quart A μ
variable {p:X→ℝ}
lemma goodX (hc:Continuous p)(h:(Radial.zone (E:=X)).Invoice p) : Integrable p Ψ:=by
       rw [quart,integrable_withDensity_iff_integrable_smul' ((sandy A μ).ennreal_ofReal) (by simp)]; simp_rw [ENNReal.toReal_ofReal (stamina A μ _),smul_eq_mul,sand,mul_assoc,mul_comm (A.kern _),← Pi.mul_apply]; exact (A.integrable_entry μ h hc).const_mul _
lemma Ppu (h:Stature p i): Pu Ψ p:=by
       intro n hn; have hv:MemLp p n Ψ:=by apply (integrable_norm_rpow_iff h.smooth.continuous.aestronglyMeasurable (by exact_mod_cast hn.ne') (by simp)).1; simp only[ENNReal.toReal_natCast,Real.rpow_natCast]; exact goodX A μ (h.smooth.continuous.norm.pow n) (h.invoice.norm.pow _)
       exact ⟨(eLpNorm p n Ψ).toReal,⟨ENNReal.toReal_nonneg,hv.1,(ENNReal.ofReal_toReal hv.2.ne).symm.le⟩⟩
section
variable [NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y][MeasurableSpace Y][BorelSpace Y]
variable (B:Law Y)(ν:Measure Y)[ν.IsAddHaarMeasure]
lemma relays (q:X×Y→ℝ)(h:Stature q i): (united A B).average (μ.prod ν) q=A.average μ (fun x=>B.average ν (fun y=>q (x,y))):=by
       let Q:=united A B; haveI : (μ.prod ν).IsAddHaarMeasure:= inferInstance
       have he : (∫ x:X×Y, (united A B).kern x ∂μ.prod ν)=(∫ x,A.kern x ∂μ)*(∫ x,B.kern x ∂ν):=by simp_rw [formed]; exact integral_prod_mul _ _
       unfold Law.average; rw [he, MeasureTheory.integral_prod _ (show Integrable _ (μ.prod ν) from runsG _ _ h)]
       simp only [Pi.mul_apply,formed]; simp_rw [show ∀ x:X, ∫ y:Y,q (x,y)*(A.kern x*B.kern y) ∂ν= (∫ y:Y,q (x,y)*B.kern y ∂ν)*A.kern x from fun i=>by simp_rw [mul_comm (A.kern i),← mul_assoc]; rw [integral_mul_const]]
       simp_rw [div_mul_eq_mul_div]; rw [integral_div]; ring
end
end YM.OPE.Borealis
