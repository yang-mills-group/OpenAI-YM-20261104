import YM.Integration.WilsonSeparatedPrefixMovingJointVote
import YM.Integration.WilsonSeparatedPrefixMovingJointPartial
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Dominated differentiation of the signed physical test before the native vote. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointPages
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}{D:ℕ}



open Set
open scoped ContDiff
open WilsonSeparatedPrefixMovingAddressInk (writer)


open MeasureTheory Set
open scoped ContDiff
variable {Ω:Type*}[MeasurableSpace Ω]{μ:Measure Ω}
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
def scroll (F:Euclid×Point4→ℝ)(hF:ContDiff ℝ ∞ F)(ξ:Euclid)(D:ℕ):Scroll D:=
  ⟨fun q=>F (ξ,q),contDiff_infty.mp (hF.comp (contDiff_const.prodMk contDiff_id)) D⟩
def field (F:Euclid×Point4→ℝ)(hF:ContDiff ℝ ∞ F)(ε y:ℝ)(s:Cover)(o:CellR)(ξ:Euclid)(D:ℕ):Volume D:=
  wheelC ε y s (scroll F hF ξ D) o
theorem native (F:Euclid×Point4→ℝ)(hF:ContDiff ℝ ∞ F)(ε y:ℝ)(s:Cover)(o:CellR)(ξ:Euclid)
    (i:Knob D)(z:Chamber):
    (field F hF ε y s o ξ D).val i z=ε^i.1.val*iteratedFDeriv ℝ i.1.val (fun q=>F (ξ,q))
      (address ε y o s z.val) (Embroider.dot ∘ i.2):=currentP ε y o s (scroll F hF ξ D) i.2 (by omega) z.val
theorem continuous (F:Euclid×Point4→ℝ)(hF:ContDiff ℝ ∞ F)(ε y:ℝ)(s:Cover)(o:CellR)(D:ℕ):
    Continuous (fun ξ=>(field F hF ε y s o ξ D).val):=by
  apply continuous_pi
  intro i
  let test:=ContinuousMultilinearMap.apply ℝ (fun _:Fin i.1.val=>Point4) ℝ (Embroider.dot ∘ i.2)
  have loc:Continuous (fun a:Euclid×Chamber=>(a.1,address ε y o s a.2.val)):=by
    apply continuous_fst.prodMk
    unfold WilsonCoeffUV.Mer.address
    fun_prop
  let joint:C(Euclid×Chamber,ℝ):=⟨fun a=>ε^i.1.val*test (iteratedFDeriv ℝ i.1.val
    (fun q=>F (a.1,q)) (address ε y o s a.2.val)),continuous_const.mul
    (test.continuous.comp ((WilsonSeparatedPrefixMovingJointPartial.original F hF i.1.val).comp loc))⟩
  apply joint.curry.continuous.congr
  intro ξ
  ext z
  exact (native F hF ε y s o ξ i z).symm
theorem original (F:Euclid×Point4→ℝ)(hF:ContDiff ℝ ∞ F)(ε y:ℝ)(s:Cover)(o:CellR)(D:ℕ)
    (income:∀n:ℕ,∃b:Euclid→ℝ,Integrable b ∧ ∀ξ q,‖iteratedFDeriv ℝ n (fun z=>F (ξ,z)) q‖≤b ξ):
    Integrable (fun ξ=>(field F hF ε y s o ξ D).val):=by
  choose b paid bound using income
  have pos (n:ℕ)(ξ:Euclid):0≤b n ξ:=(norm_nonneg _).trans (bound n ξ 0)
  have total:Integrable (fun ξ=>∑n∈Finset.range (D+1),|ε|^n*b n ξ):= by
    apply integrable_finsetSum;intro n _;exact (paid n).const_mul _
  apply total.mono' (continuous F hF ε y s o D).aestronglyMeasurable
  filter_upwards [] with ξ
  apply Embroider.vote_cap (field F hF ε y s o ξ D) (Finset.sum_nonneg fun n _=>mul_nonneg (pow_nonneg (abs_nonneg _) _) (pos _ _))
  intro i z
  rw [native,norm_mul,norm_pow,Real.norm_eq_abs]
  have moment:‖iteratedFDeriv ℝ i.1.val (fun q=>F (ξ,q)) (address ε y o s z.val) (Embroider.dot ∘ i.2)‖≤b i.1.val ξ:=
    (ContinuousMultilinearMap.le_opNorm _ _).trans (by
      simp only [Function.comp_apply,Embroider.dot,Pi.norm_single,norm_one,Finset.prod_const_one,mul_one]
      exact bound _ _ _)
  exact (mul_le_mul_of_nonneg_left moment (pow_nonneg (abs_nonneg _) _)).trans
    (Finset.single_le_sum (fun n _=>mul_nonneg (pow_nonneg (abs_nonneg ε) n) (pos n ξ)) (Finset.mem_range.mpr i.1.isLt))
end YM.Integration.WilsonSeparatedPrefixMovingJointPages
