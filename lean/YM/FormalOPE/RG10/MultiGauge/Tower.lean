import YM.FormalOPE.RG10.MultiGauge.Splice
import YM.PertExtension.GaussianIBP
/-!
 # normalized Fubini step for genuine joint Hessian

 Mean shift is exact gaussian conditioning. Left-out determinant/trivial Haar normalization
 disappears from *ratio*, not claiming its constancy when changing gauge or schedule.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MultiGauge
open Function Filter Topology Set MeasureTheory Measure PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius ENNReal
variable {E F K : Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F][MeasurableSpace F][BorelSpace F]
 [NormedAddCommGroup K][NormedSpace ℝ K][FiniteDimensional ℝ K][MeasurableSpace K][BorelSpace K]
namespace Splice
variable (Λ:Law E)(d:(F × K) ≃ₗ[ℝ] E)
variable (μ:Measure E)[IsAddHaarMeasure μ](ν : Measure F)[IsAddHaarMeasure ν] (ρ : Measure K)[IsAddHaarMeasure ρ]

-- Appendix Fub via uniqueness of additive Haar up to constants. Doesn't claim normalization in µ is 1!
private def S (d:(F × K) ≃ₗ[ℝ] E) := map (fusion Λ d) (ν.prod ρ)
private instance iS : IsAddHaarMeasure (Splice.S Λ ν ρ d):= (fusion Λ d).toContinuousLinearEquiv.isAddHaarMeasure_map _

private def flux : NNReal := addHaarScalarFactor (Splice.S Λ ν ρ d) μ
private lemma supply : Splice.S Λ ν ρ d=(flux Λ d μ ν ρ) • μ:= isAddLeftInvariant_eq_smul _ _
lemma kernel_int : Integrable Λ.kern μ:= by
 have he:= Λ.integrable_entry (A:=1) μ (Zone.Invoice.const (1:ℝ)) continuous_const; rwa [one_mul] at he
lemma positive : 0<(∫ x:E, Λ.kern x ∂μ):= integral_exp_pos (kernel_int Λ μ)
omit [FiniteDimensional ℝ E] in
private lemma mass_pos : 0<flux Λ d μ ν ρ:= addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
private lemma price_map (f:E→ℝ):
 (∫ z:F×K, f (fusion Λ d z) ∂ν.prod ρ)= (flux Λ d μ ν ρ: ℝ) * ∫ x,f x ∂μ:= by
 let e:= (fusion Λ d).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
 calc
    _ = ∫ x,f x ∂Splice.S Λ ν ρ d:= (integral_map_equiv e f).symm
    _ = _:= by rw [supply Λ d μ, integral_smul_nnreal_measure]; rfl

theorem splice_int (f:E→ℝ)(hi:Integrable (f * Λ.kern) μ): Λ.average μ f = (rest Λ d).average ρ (fun b=> (fast Λ d).average ν (fun x=> f (fusion Λ d (x,b)))) := by
 let a:= fast Λ d; let g:= rest Λ d; let D:=flux Λ d μ ν ρ
 let w:=fun x=> (f * Λ.kern) (fusion Λ d x)
 let W (x:F)(y:K):= f (fusion Λ d (x,y))*a.kern x
 let R:= ∫ y:K,(∫ x:F,W x y ∂ν)*g.kern y ∂ρ
 let r:= (∫ x:F×K, w x ∂ν.prod ρ)
 let U:= ∫ y:K,g.kern y ∂ρ; let V:=∫ x:F,a.kern x ∂ν; let B:=∫ x:E,Λ.kern x ∂μ
 have he:R=r:= by
    have he x y:w (x,y)= W x y * g.kern y:= by unfold w W a g; simp [stamp,mul_assoc]
    have hi': Integrable (f * Λ.kern) (Splice.S Λ ν ρ d):= by rw [supply Λ d μ]; exact hi.smul_measure_nnreal -- syntax
    unfold r; rw [integral_prod_symm w (hi'.comp_aemeasurable (fusion Λ d).toContinuousLinearEquiv.continuous.aemeasurable)]; simp_rw [he,integral_mul_const]; rfl
 have hn : V*U=(D:ℝ)*B := by rw [← price_map]; unfold V U; rw [← integral_prod_mul (μ:=ν) (ν:=ρ) a.kern g.kern]; exact integral_congr_ae (Eventually.of_forall (fun ⟨_,_⟩=> (stamp ..).symm)) -- dependent
 have hd:0<(D:ℝ):= mass_pos Λ d μ ν ρ
 have hu:0<U:= positive (rest Λ d) _
 have hv:0<V:= positive (fast Λ d) _
 have hb:0<B:= positive Λ μ
 have hr: (D:ℝ) * (∫ x:E,(f*Λ.kern) x ∂μ)=r:= (price_map Λ d μ ν ρ (f*Λ.kern)).symm
 unfold Law.average; change _ / B=(∫ y:K, ((∫ x:F,W x y ∂ν)/V)*g.kern y ∂ρ)/ U
 simp_rw [show ∀ y:K, ((∫ x:F,W x y ∂ν)/V)*g.kern y=((∫ x:F,W x y ∂ν)*g.kern y)/V from fun y=>by ring, integral_div];
 change _ / B= R/V/U; rw [div_div,hn,he,← hr,mul_div_mul_left ..]; exact hd.ne'
end Splice
end YM.FormalOPE.RG10.MultiGauge
