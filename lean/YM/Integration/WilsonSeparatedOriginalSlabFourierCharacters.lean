import YM.Integration.WilsonSeparatedOriginalSlabFourierRoom
import YM.Integration.WilsonSeparatedOriginalSlabFourierJets

/-! Actual integer Fourier modes read as the physical source's deposited three-plane waves with their true rescaling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierCharacters
open Finset Function UnitAddTorus RG05Readout RG05Readout.Native RG05Readout.Pulse
open WilsonSeparatedOriginalSlabFourierPositions WilsonSeparatedOriginalSlabFourierRoom WilsonSeparatedOriginalSlabPlaneTest
open scoped BigOperators Classical Topology

def wire (P c:ℝ)(k:Axes→ℤ)(i:Fin 3)(d:Axis):ℝ:=(2*Real.pi)*P⁻¹*(c⁻¹*(k (i,d):ℝ))

theorem original (P:ℝ){c:ℝ}(cp:c≠0)(k:Axes→ℤ)(x:Cloud (Fin 3)):
    (packet (wire P c k) c).val x=WilsonSeparatedOriginalSlabFourierJets.wave (cursor P) k x:=by
  have arg:(∑i:Fin 3,∑d:Axis,wire P c k i d*(c • x i) d)=WilsonSeparatedOriginalSlabFourierSymbol.arm k (cursor P x):=by
    unfold WilsonSeparatedOriginalSlabFourierSymbol.arm
    simp only [smul_apply,_root_.sum_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]
    rw [Fintype.sum_prod_type,Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _=>?_)
    rw [Finset.mul_sum];refine Finset.sum_congr rfl (fun d _=>?_)
    change ((2*Real.pi)*P⁻¹*(c⁻¹*(k (i,d):ℝ)))*(c*(x i) d)=(2*Real.pi)*((k (i,d):ℝ)*(P⁻¹*(x i) d))
    field_simp
  change (∏i:Fin 3,Complex.exp (((∑d:Axis,wire P c k i d*(c • x i) d:ℝ):ℂ)*Complex.I))=_
  rw [←Complex.exp_sum,←Finset.sum_mul,←Complex.ofReal_sum,arg]
  exact (WilsonSeparatedOriginalSlabFourierSymbol.source k (cursor P x)).symm

end YM.Integration.WilsonSeparatedOriginalSlabFourierCharacters
