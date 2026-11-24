import YM.Integration.WilsonIndependentSpoutSchurVote
import YM.Integration.WilsonIndependentSpoutThermalLog
import YM.Integration.WilsonIndependentConditionalPositiveVacuum

/-! The same normalized thermal integral returns the finite lower action
and its complete field-independent scalar. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutSchurVacuum
open Matrix PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue
open PertExtension FreeResolvent Metric Lattice RG Wilson Tree Precision Exterior Next.Free
open WilsonIndependentSpoutSchurFrame WilsonIndependentSpoutSchurVote
open WilsonIndependentSpoutThermalLog
open WilsonIndependentConditionalPositiveVacuum (value)
open scoped Classical BigOperators MatrixOrder
variable {G:Gauge}{c f:Lattice.Side}(S:StepData c f)(T:Forest S.ratio)
  (H Y:FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)

def read (A:Cost)(Ñ:ChartRatio G)(P:PChart G f):Ink (Woods G c):=
  Wick (Woods G c) (treeInverse G S T H 0) (raiseE (field S T H Y Q A Ñ P))

def deposited (A:Cost)(Ñ:ChartRatio G):Cost:=
  Bank.reel A (plugζ S Ñ)-logOf ((A⁻¹)^Fintype.card (Active G T))

theorem original (A:Cost)(unit:constantCoeff A=1){Ñ:ChartRatio G}{P:PChart G f}
    (p:shellK 2 P)(base:P 0=shine (orbQ (precisionC G f H)))(hz:S.patch.Branches S.kernel G)
    (hu:Inputs S Q (H.acts f) (Y.acts c))(hs:(H.acts f).transpose=H.acts f)
    (ratio:LocalRatio Ñ)(hf:(treeMatrix G S T H).PosDef)(pure:∀i,Pure (P i)):
    logOf (read S T H Y Q A Ñ P)=orbC (precisionC G c Y)-
      redo A (flash (winter S T H Y Q Ñ P))+soil (deposited S T A Ñ):=by
  let D:=read S T H Y Q A Ñ P
  let j:Cost:=(A⁻¹)^Fintype.card (Active G T)
  let a:=bias A (orbC (precisionC G c Y))
  let f:=inside S T H Q Ñ P
  have pay:=WilsonIndependentSpoutSchurVote.original S T H Y Q A unit p base hz hu hs ratio hf 1
  simp only [map_one,mul_one] at pay
  change D*soil j=raiseE a*redo A f at pay
  have hi:constantCoeff j=1:=by simp [j,constantCoeff_inv,unit]
  have hj:constantCoeff (soil (U:=Woods G c) j)=1:=by rw [soil_head,hi,map_one]
  have ha:constantCoeff a=0:=zero A unit _
  have hzX:constantCoeff (redo (U:=Woods G c) A X)=0:=by rw [redo_X];simp
  have hin:constantCoeff f=1:=inside_mass S T H Q ratio
  have hrf:=floor₁ _ hzX hin
  have hd:constantCoeff D=1:=by
    have he:=congrArg constantCoeff pay
    simpa only [map_mul,hj,mul_one,raise_one ha,hrf] using he
  have hload:constantCoeff (soil (U:=Woods G c) X)=0:=by simp [soil]
  have hlog:=congrArg logOf pay
  rw [log_product D _ hd hj,←log_map _ hload hi,Blue.Cameo.log_health hrf ha,
    ←log_map _ hzX hin] at hlog
  rw [winter_read S T H Y Q p ratio hz hs pure,map_add,map_sub,
    show redo A (orbC (precisionC G c Y))=soil A⁻¹^2*orbC (precisionC G c Y) from redo_palm ..,
    WilsonIndependentSpoutThermalLog.cash,deposited,map_sub]
  change logOf D=_
  change logOf D+soil (U:=Woods G c) (logOf j)=bias A (orbC (precisionC G c Y))+redo A (logOf f) at hlog
  unfold bias at hlog
  linear_combination hlog

theorem held (A:Cost)(unit:constantCoeff A=1){Ñ:ChartRatio G}{P:PChart G f}
    (p:shellK 2 P)(base:P 0=shine (orbQ (precisionC G f H)))(hz:S.patch.Branches S.kernel G)
    (hu:Inputs S Q (H.acts f) (Y.acts c))(hs:(H.acts f).transpose=H.acts f)
    (ratio:LocalRatio Ñ)(hf:(treeMatrix G S T H).PosDef)(pure:∀i,Pure (P i))(e:ℕ)(b:TreeVars G c):
    value (logOf (read S T H Y Q A Ñ P)) e b=
    value (orbC (precisionC G c Y)) e b-value (flash (mix A (winter S T H Y Q Ñ P))) e b:=by
  rw [original S T H Y Q A unit p base hz hu hs ratio hf pure,
    redo_stern _ (winter_band S T H Y Q ratio p)]
  simp only [value,map_add,map_sub,soil,coeff_map,MvPolynomial.eval_C]
  ring

end YM.Integration.WilsonIndependentSpoutSchurVacuum
