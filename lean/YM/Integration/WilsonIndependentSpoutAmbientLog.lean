import YM.Integration.WilsonIndependentSpoutPostedBank
import YM.Integration.WilsonIndependentConditionalRawVacuum
import YM.Integration.WilsonIndependentConditionalMerShift

/-! The ordinary full-axis connected vacuum at a held field, with the actual
covariance moved through the finite active tree. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutAmbientLog
open Function PowerSeries Matrix WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open Finset
open scoped BigOperators Classical Matrix
variable {U I J:Type}[Fintype U][Fintype I][Fintype J]

theorem graded (C:Matrix U U ℝ){P:Pal ℝ U}(scope:shellK 2 P)(bare:P 0=0):
    stopF 1 (ramp (abr C P) 2)=flash (WilsonIndependentConditionalRawVacuum.finite C P):=by
  rw [at_one _ _ (stops_abr C scope bare)]
  apply congrArg Blue.flash;funext e
  change ∑ j∈Finset.range (1+2+3*e),abr C P j e=∑ j∈Finset.range (3*e+1),abr C P j e
  apply (Finset.sum_subset (Finset.range_mono (by omega)) ?_).symm
  intro j _ hj;simp only [mem_range,not_lt] at hj
  funext r;exact span_abr C scope bare j e r (Or.inr (by omega))

theorem projected (D:Matrix U (I⊕J) ℝ)(C:Matrix I I ℝ)(adj:C.transpose=C){P:Pal ℝ U}
    (scope:shellK 2 P)(bare:P 0=0)(pure:∀e,Pure (P e)):
    logOf (Wick J C (raiseE (loom D (Blue.flash P))))=
      projectZero (loom D (Blue.flash (WilsonIndependentConditionalRawVacuum.finite
        (D*fillSlots J C*D.transpose) P))):=by
  let K:=D*fillSlots J C*D.transpose
  let S:=stopF 1 (ramp (abr K P) 2)
  have P0:constantCoeff (Blue.flash P)=0:=by
    rw [←coeff_zero_eq_constantCoeff_apply,Blue.flash,coeff_mk,bare];simp [totalR]
  have S0:constantCoeff S=0:=by
    rw [←coeff_zero_eq_constantCoeff_apply];change (coeff 0) (stopF 1 (ramp (abr K P) 2))=0
    rw [stopF,coeff_map,coeff_zero_eq_constantCoeff_apply,rolls_clean K bare,map_zero]
  have ld:constantCoeff (loom D S)=0:=by rw [←coeff_zero_eq_constantCoeff_apply,loom,coeff_map,coeff_zero_eq_constantCoeff_apply,S0,map_zero]
  have hc:(fillSlots J C).transpose=fillSlots J C:=by simp [fillSlots,Matrix.fromBlocks_transpose,adj]
  have top:Wick J C (raiseE (loom D (Blue.flash P)))=raiseE (projectZero (loom D S)):=by
    rw [←raise_map (loom D) (by simp [loom]) P0,Wick,
      WilsonIndependentConditionalMerShift.heat D _ hc,as_normal_exp _ scope bare pure,
      raise_map (loom D) (by simp [loom]) S0,raise_map projectZero (by simp [projectZero]) ld]
  rw [top,←graded K scope bare]
  apply raise_inj (constantCoeff_logOf (raise_one (coeff_proj ld))) (coeff_proj ld)
  exact raising_log (raise_one (coeff_proj ld))

end YM.Integration.WilsonIndependentSpoutAmbientLog
