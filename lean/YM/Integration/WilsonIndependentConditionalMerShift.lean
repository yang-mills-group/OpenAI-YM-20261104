import YM.Integration.WilsonIndependentConditionalUnshiftedExit
import YM.Integration.WilsonIndependentConditionalPostedMean
import YM.WilsonCoeffUV.Wick.Lift

/-! Naturality of the entire normalized finite Mer heat under the true
predictor shear, on all retained fields. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalMerShift
open Function Matrix Lattice RG WilsonCoeffUV Laurent Bloch Metric WilsonCoeffUV.Blue
open FreeResolvent Work.F08 WilsonCoeffUV.Bank Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil Precision Embroider RegulatorIR RegulatorIR.Diagram
open PowerSeries
open scoped BigOperators Classical
variable {U V:Type}[Fintype U][Fintype V]

theorem heat (D:Matrix U V ℝ)(C:Matrix V V ℝ)(hc:C.transpose=C)(f:Ink U):
    blur C (loom D f)=loom D (blur (D*C*D.transpose) f):=by
   ext1 i
   simp only [blur,overlay_apply,loom,coeff_map]
   change glaze C (cord D (coeff i f))=cord D (glaze (D*C*D.transpose) (coeff i f))
   exact Bank.Carp.daystar D C hc (coeff i f)

def carried (C:Matrix U U ℝ)(P w:ℕ→Gen ℝ U)(l:ℕ):Ink U:=
  stopF 1 (ramp (bul C (abr C P) w) l)

private theorem initial {P:ℕ→Gen ℝ U}(z:P 0=0):constantCoeff (flash P)=0:=by
  rw [←coeff_zero_eq_constantCoeff_apply,flash,coeff_mk,z]
  simp [totalR]

theorem quotient (D C:Matrix U U ℝ)(hc:C.transpose=C)(fixed:D*C*D.transpose=C)
    {p q w v:ℕ→Gen ℝ U}{l:ℕ}(ap:shellK 2 p)(aq:shellK 2 q)(wp:shellK l w)(wq:shellK l v)
    (zp:p 0=0)(zq:q 0=0)(hp:∀i,Pure (p i))(hq:∀i,Pure (q i))(hw:∀i,Pure (w i))(hv:∀i,Pure (v i))
    (action:loom D (flash p)=flash q)(operand:loom D (flash w)=flash v):
    loom D (carried C p w l)=carried C q v l:=by
  have E:loom D (raiseE (flash p))=raiseE (flash q):=by
    rw [raise_map (loom D) (by simp [loom]) (initial zp),action]
  have commute (f:Ink U):loom D (blur C f)=blur C (loom D f):=by
    have id:=heat D C hc f
    rw [fixed] at id
    exact id.symm
  have debt:constantCoeff (blur C (raiseE (flash q)))=1:=by
    rw [←coeff_zero_eq_constantCoeff_apply,blur,overlay_apply]
    rw [coeff_zero_eq_constantCoeff_apply,raise_one (initial zq),glaze_one]
  have nonzero:blur C (raiseE (flash q))≠0:=by
    intro zero;rw [zero,map_zero] at debt;exact zero_ne_one debt
  apply mul_left_cancel₀ nonzero
  unfold carried
  calc
    _=loom D (blur C (raiseE (flash p)) *stopF 1 (ramp (bul C (abr C p) w) l)):=by rw [map_mul,commute,E]
    _=loom D (blur C (raiseE (flash p)*flash w)):=congrArg _ (as_column C ap zp hp wp hw).symm
    _=blur C (raiseE (flash q)*flash v):=by rw [commute,map_mul,E,operand]
    _=_:=as_column C aq zq hq wq hv

variable {G:Gauge}{c f:Side}
theorem fixed (M:Matrix (Woods G f) (Woods G c) ℝ)(H:Matrix (Woods G f) (Woods G f) ℝ):
    groundM G M*fillSlots (Woods G c) H*(groundM G M).transpose=fillSlots (Woods G c) H:=by
  simp [groundM,fillSlots,Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply]

theorem original (S:StepData c f)(Ñ:ChartRatio G)(H:Matrix (Woods G f) (Woods G f) ℝ)
    (adj:H.transpose=H)(M:Matrix (Woods G f) (Woods G c) ℝ){P w:PChart G f}{k:ℕ}
    (p:shellK 2 P)(r:LocalRatio Ñ)(flags:S.patch.Branches S.kernel G)(h:shellK k w)
    (hp:∀i,Pure (P i))(hw:∀i,Pure (w i)):
    loom (groundM G M) (carried (fillSlots (Woods G c) H) (casePW S Ñ 0 P) (srCold w 0) k)=
      carried (fillSlots (Woods G c) H) (casePW S Ñ M P) (srCold w M) k:=by
  apply quotient _ _ _ (fixed M H) (pack_band S p) (pack_band S p) (fade_shell _ h) (fade_shell _ h)
    (pack_zero S r) (pack_zero S r) (pack_pure S r flags hp) (pack_pure S r flags hp)
    (fun i=>fade_pure (hw i) _) (fun i=>fade_pure (hw i) _)
    (WilsonIndependentConditionalPostedMean.vacuum S Ñ M p) (WilsonIndependentConditionalPostedMean.mark M h)
  simp [fillSlots,Matrix.fromBlocks_transpose,adj]

end YM.Integration.WilsonIndependentConditionalMerShift
