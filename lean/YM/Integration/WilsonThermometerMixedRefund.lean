import YM.Integration.WilsonThermometerMixedGallery
import YM.Integration.WilsonThermometerCenteredAlgebra

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedRefund
open Finset Marker QuadraticLocal MeasureTheory WilsonThermometerMixedAmplitude WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

def reading (Q M:Poly J):ℂ:=(total M Q).part full

/-- Both amplitudes use all the faces of the same inverse ordinary table. -/
theorem filed {q:ℂ}{A K F:Poly J}(cert:Line q A K F)(Q:Poly J):
    reading Q K-reading Q A=q*(reading Q F-reading Q A):=by
  have point (s:(J).Mode):K.part s=A.part s+q*(F.part s-A.part s):=
    congrArg (fun z:Poly J=>z.part s) cert.value
  simp only [reading,affine,←sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro s mem
  rw [point]
  ring

/-- A single large old mixed charge can be withdrawn after the complete signed reading,
including any common reference value of the two independently priced endpoints. -/
theorem paid {g:ℝ}(positive:0≤g)(p l:ℕ){A K F:Poly J}
    (cert:Line ((g:ℂ)^(p+(l+92))) A K F)(Q:Poly J)(reference:ℂ)(E₀ E₁:ℝ)
    (erased:g^(l+92)*‖reading Q A-reference‖≤E₀)
    (enlarged:g^(l+92)*‖reading Q F-reference‖≤E₁):
    ‖reading Q K-reading Q A‖≤g^p*(E₁+E₀):=by
  rw [filed cert Q,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg positive,pow_add,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg positive _)
  have price:‖reading Q F-reading Q A‖≤‖reading Q F-reference‖+‖reading Q A-reference‖:=by
    simpa only [norm_sub_rev (reading Q A) reference] using
      (norm_sub_le_norm_sub_add_norm_sub (reading Q F) reference (reading Q A))
  have h:=mul_le_mul_of_nonneg_left price (pow_nonneg positive (l+92))
  rw [mul_add] at h
  exact h.trans (add_le_add enlarged erased)

/-- Integrate every subword with the original older law and its one global mass before
applying the aperture rebate. The model bench and its regular covariances stay common. -/
theorem original {Y:Type*}[MeasurableSpace Y](μ:Measure Y)(mass:ℂ)(A K F:Y→Poly J)
    {g:ℝ}(positive:0≤g)(p l:ℕ)
    (program:∀y,Line ((g:ℂ)^(p+(l+92))) (A y) (K y) (F y))
    (base:∀s,Integrable (fun y=>(A y).part s) μ)
    (raised:∀s,Integrable (fun y=>(F y).part s) μ)
    (Q:Poly J)(reference:ℂ)(E₀ E₁:ℝ)
    (erased:g^(l+92)*‖reading Q (WilsonOriginalSignedHardHearing.mean μ mass A)-reference‖≤E₀)
    (enlarged:g^(l+92)*‖reading Q (WilsonOriginalSignedHardHearing.mean μ mass F)-reference‖≤E₁):
    ‖reading Q (WilsonOriginalSignedHardHearing.mean μ mass K)-
      reading Q (WilsonOriginalSignedHardHearing.mean μ mass A)‖≤g^p*(E₁+E₀):=by
  exact paid positive p l (WilsonThermometerMixedGallery.older μ mass A K F program base raised)
    Q reference E₀ E₁ erased enlarged

end YM.Integration.WilsonThermometerMixedRefund
