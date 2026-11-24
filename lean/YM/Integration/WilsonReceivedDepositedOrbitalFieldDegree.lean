import YM.Integration.WilsonOriginalCensusFinitePortrait
import YM.Integration.WilsonThermometerOriginalPupilDegree

/-! A filed angular tensor retains its uniform degree under each original linear field coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalFieldDegree
open Finset Comparison.RG02 Comparison.RG02.Valence WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonNeutralTwoPrintPathJet (diagonal)
open private monomial from YM.Integration.WilsonThermometerOriginalPupilDegree
open scoped Classical BigOperators

variable {W E:Type}[Fintype W][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
theorem layer (L:E→ₗ[ℝ](W→ℝ))(d:ℕ)(T:Ten ℝ W d):
    Level (d:ℤ) (fun y:E=>(MvPolynomial.eval (L y) (paint d T):ℂ)):=by
  let port (w:W):E→L[ℝ]ℂ:=Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap ((LinearMap.proj w).comp L))
  simp only [toll,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod]
  apply Level.total
  intro z _
  have first:=monomial (univ:Finset (Fin d)) (fun u=>port (z u)) (fun u=>Level.linear (port (z u)))
  simpa [port] using first.factor ((T z:ℝ):ℂ)

theorem original (L:E→ₗ[ℝ](W→ℝ))(cap:ℕ)(T:Gen ℝ W):
    Level (cap:ℤ) (fun y:E=>(diagonal cap T (L y):ℂ)):=by
  simp only [diagonal,Complex.ofReal_sum]
  apply Level.total
  intro d hd
  exact (layer L d (T d)).promote (by exact_mod_cast mem_range_succ_iff.mp hd)

end YM.Integration.WilsonReceivedDepositedOrbitalFieldDegree
end
