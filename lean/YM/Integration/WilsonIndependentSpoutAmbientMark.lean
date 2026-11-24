import YM.Integration.WilsonIndependentSpoutAmbientLog
import YM.Integration.WilsonIndependentConditionalRawSpout

/-! Exact normalized marked heat on the active axes of the original finite spring. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutAmbientMark
open Function PowerSeries Matrix WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open Finset
open scoped BigOperators Classical Matrix
variable {U I J:Type}[Fintype U][Fintype I][Fintype J]

theorem graded (C:Matrix U U ℝ){P W:Pal ℝ U}{k:ℕ}(scope:shellK 2 P)(bare:P 0=0)
    (span:shellK k W):
    stopF 1 (ramp (bul C (abr C P) W) k)=
      flash (WilsonIndependentConditionalRawSpout.finite C P W k):=by
  rw [at_one _ _ (stops_bul C (span_abr C scope bare) k span)]
  apply congrArg Blue.flash;funext e
  change ∑ j∈Finset.range (1+k+3*e),bul C (abr C P) W j e =
    ∑ j∈Finset.range (k+3*e+1),bul C (abr C P) W j e
  rw [show 1+k+3*e=k+3*e+1 by omega]

theorem projected (D:Matrix U (I⊕J) ℝ)(C:Matrix I I ℝ)(adj:C.transpose=C)
    {P W:Pal ℝ U}{k:ℕ}(scope:shellK 2 P)(bare:P 0=0)(pure:∀e,Pure (P e))
    (span:shellK k W)(smooth:∀e,Pure (W e)):
    Wick J C (raiseE (loom D (Blue.flash P))*loom D (Blue.flash W))=
        Wick J C (raiseE (loom D (Blue.flash P)))*projectZero (loom D (Blue.flash
          (WilsonIndependentConditionalRawSpout.finite (D*fillSlots J C*D.transpose) P W k))):=by
  have p0:constantCoeff (Blue.flash P)=0:=by
    rw [←coeff_zero_eq_constantCoeff_apply,Blue.flash,coeff_mk,bare];simp [totalR]
  have hc:(fillSlots J C).transpose=fillSlots J C:=by simp [fillSlots,Matrix.fromBlocks_transpose,adj]
  rw [←raise_map (loom D) (by simp [loom]) p0,←map_mul,Wick,Wick,
    WilsonIndependentConditionalMerShift.heat D _ hc,WilsonIndependentConditionalMerShift.heat D _ hc,
    as_column _ scope bare pure span smooth,graded _ scope bare span,map_mul,map_mul]

end YM.Integration.WilsonIndependentSpoutAmbientMark
