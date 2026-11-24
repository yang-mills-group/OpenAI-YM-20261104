import YM.Integration.WilsonSeparatedPrefixMovingJointPages
import YM.Integration.WilsonSeparatedPrefixMovingJointKernel
import YM.Integration.WilsonSeparatedPrefixMovingJointPartial
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Dominated differentiation of the signed physical test before the native vote. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointWavePages
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
open WilsonSeparatedPrefixMovingJointExpansion (angle)
open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonSeparatedPrefixMovingJointSpectrum (physical)
open WilsonSeparatedPrefixMovingJointIntegral (growth multiplier)
def pulse (χ:Rarity D)(d:Bool)(a:Euclid×Point4):ℝ:=(sheet χ (angle a.1) d).ψ.val a.2
theorem smooth (χ:Rarity D)(hχ:ContDiff ℝ ∞ χ.ψ.val)(d:Bool):ContDiff ℝ ∞ (pulse χ d):=by
  have angular:ContDiff ℝ ∞ (fun a:Euclid×Point4=>angle a.1 a.2):=by
    change ContDiff ℝ ∞ (fun a:Euclid×Point4=>(2*Real.pi)*inner ℝ a.1 (physical.symm a.2))
    exact contDiff_const.mul (contDiff_fst.inner ℝ (physical.symm.contDiff.comp contDiff_snd))
  exact (hχ.comp contDiff_snd).mul ((WilsonSeparatedPrefixMovingJointWaves.smooth d).comp angular)
theorem original (χ:Rarity D)(hχ:ContDiff ℝ ∞ χ.ψ.val):
    ∃M:ℝ,0≤M ∧ ∀(d:Bool)(ε y:ℝ)(s:Cover)(o:CellR),0≤ε→ε≤1→
    let sheetAt:=fun ξ=>wheelC ε y s (sheet χ (angle ξ) d).ψ o
    Continuous sheetAt ∧ ∀ξ,‖sheetAt ξ‖≤M*(1+‖ξ‖^D):=by
  obtain ⟨A,apos,ink⟩:=WilsonSeparatedPrefixMovingJointWaves.original χ hχ
  have cm:0≤ multiplier:=by unfold multiplier;positivity
  refine ⟨A*multiplier^D,mul_nonneg apos (pow_nonneg cm _),?_⟩
  intro d ε y s o pos cap pane
  refine ⟨?_,?_⟩
  · exact Continuous.subtype_mk (WilsonSeparatedPrefixMovingJointPages.continuous (pulse χ d) (smooth χ hχ d) ε y s o D) _
  intro ξ
  have charge:=amplitudes_bound ε y (ink (angle ξ) d) pos cap o s
  exact charge.trans ((mul_le_mul_of_nonneg_left (growth D ξ) apos).trans_eq (mul_assoc _ _ _).symm)
end YM.Integration.WilsonSeparatedPrefixMovingJointWavePages
