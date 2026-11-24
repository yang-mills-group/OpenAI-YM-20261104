import YM.Integration.WilsonIndependentSpoutScaledPrimitive

/-! Real positive, bare-anchored scale witnesses for the finite thermal
jets of a prescribed Spout course. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutClockWitness
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Ward RegulatorIR.Geometry RegulatorIR.Prim RegulatorIR.Binding
open RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Calibration RegulatorIR.Profiles
open Finset PertExtension PertExtension.Series PertExtension.Series.Radial
open PertExtension.Series.Tested PowerSeries Filter
open scoped Classical Topology BigOperators ContDiff PowerSeries

private theorem cut (A:Writing)(p:ℕ):
    Squares p (∑i∈range (p+1),PowerSeries.X^i*PowerSeries.C (coeff i A)) A:=by
  intro i hi
  rw [map_sum,sum_eq_single_of_mem i (mem_range.mpr (by omega)),coeff_X_pow_mul',
    if_pos (by omega),tsub_self,PowerSeries.coeff_C]
  · simp
  · intro j _ ne;rw [coeff_X_pow_mul']
    split
    · rw [PowerSeries.coeff_C,if_neg (by omega)]
    · rfl

theorem buy (p:ℕ)(A:Writing)(unit:constantCoeff A=1):
    ∃K:Feeds,Squares p (tale K.dine) A∧Squares p (tale K.scale.beta) ((A⁻¹)^2):=by
  let g (x:ℝ):=∑ i∈Finset.range (p+1),x^i*coeff i A
  have continuous:Continuous g:=by unfold g;fun_prop
  have smooth:ContDiffAt ℝ ∞ g 0:=by unfold g;fun_prop
  have known:Squares p (tale g) A:=by
    intro i hi
    let z (j:ℕ)(x:ℝ):=x^j
    let f (j:ℕ):ℝ→ℝ:=z j*(fun _=>coeff j A)
    have h₀ j:ContDiffAt ℝ ∞ (f j) 0:=(contDiffAt_id.pow _).mul contDiffAt_const
    rw [show g=∑j∈Finset.range (p+1),f j from funext (fun x=>(Finset.sum_apply x _ f).symm),
      tale_sum]
    rw [←cut A p i hi]
    apply congr_arg
    refine Finset.sum_congr rfl fun j _=>?_
    rw [show tale (f j)=_ from tale_mul (f:=z j) (g:=fun _=>coeff j A)
      (contDiffAt_id.pow _) contDiffAt_const,tale_const]
    apply congr_arg (· * _)
    exact Script.dictates (f:=fun x:ℝ=>x^j) (contDiffAt_id.pow _) (Script.predicts_pow _)
    exact fun j _=>h₀ j
  have origin:g 0=1:=by rw [←tale_base (f:=g),known 0 (by omega),coeff_zero_eq_constantCoeff_apply,unit]
  obtain ⟨K,kg⟩:=Feeds.admits continuous smooth origin
  have k0:Squares p (tale K.dine) A:=by rwa [tale_eq smooth kg]
  refine ⟨K,k0,?_⟩
  rw [WilsonIndependentSpoutScaledPrimitive.scale,pow_two,pow_two]
  have zero:coeff 0 A=1:=by rwa [coeff_zero_eq_constantCoeff_apply]
  have inv:=inv_v k0 (by rw [k0 0 (by omega),zero];norm_num) (by rw [zero];norm_num)
  exact inv.maintains inv

theorem original {W:Type}{d:W→ℕ}(p:ℕ)(A:Page d→Writing)
    (unit:∀v,constantCoeff (A v)=1)(bare:∀w,A (Page.opening d w)=1):
    ∃K:Tent d,(∀w,K (Page.opening d w)=Calibration.dawn)∧∀v,
      Squares p (tale (K v).dine) (A v)∧
      Squares p (tale (sheet K v).beta) (((A v)⁻¹)^2):=by
  choose F Fp using fun v=>buy p (A v) (unit v)
  let K:Tent d:=fun v=>if v=Page.opening d v.bindW then Calibration.dawn else F v
  refine ⟨K,fun w=>by exact if_pos rfl,fun v=>?_⟩
  by_cases h:v=Page.opening d v.bindW
  · have top:A v=1:=h ▸ bare _
    have hK:K v=Calibration.dawn:=if_pos h
    change Squares p (tale (K v).dine) (A v)∧Squares p (tale (K v).scale.beta) _
    rw [hK,top,WilsonIndependentSpoutScaledPrimitive.scale,
      show tale Calibration.dawn.dine=1 from (tale_const 1).trans (map_one _)]
    simp only [inv_one,one_pow]
    exact ⟨fun _ _=>rfl,fun _ _=>rfl⟩
  · simpa only [K,if_neg h,sheet,Function.comp_apply] using Fp v

end YM.Integration.WilsonIndependentSpoutClockWitness
