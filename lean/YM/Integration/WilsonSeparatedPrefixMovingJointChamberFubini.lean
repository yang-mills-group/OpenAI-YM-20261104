import YM.Integration.WilsonSeparatedPrefixMovingJointChamberWord
import Mathlib.MeasureTheory.Integral.Prod
import YM.Integration.WilsonSeparatedPrefixMovingJetService
import YM.Integration.WilsonSeparatedPrefixMovingJointWavePages
import YM.Integration.WilsonSeparatedPrefixMovingJointFarBook
import YM.Integration.WilsonSeparatedPrefixMovingJointWord
import YM.Integration.WilsonSeparatedPrefixMovingJointPages
import YM.Integration.WilsonSeparatedPrefixMovingJointDerivatives
import YM.Integration.WilsonSeparatedPrefixMovingJointIntegral
import YM.Integration.WilsonSeparatedPrefixMovingJointPartial
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Dominated differentiation of the signed physical test before the native vote. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointChamberFubini
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
open WilsonSeparatedPrefixMovingJointWaves (sheet wave)
open WilsonSeparatedPrefixMovingJointExpansion (angle coefficient coin)
open WilsonSeparatedPrefixMovingJointSpectrum (physical)
open WilsonSeparatedPrefixMovingJointIntegral (growth multiplier)
open scoped SchwartzMap
variable {E:ℕ}
open WilsonSeparatedPrefixMovingJointKernel (ink)
open WilsonSeparatedPrefixMovingJointKernelRead (painted)
open WilsonSeparatedPrefixMovingJointPages (field)
open WilsonSeparatedPrefixMovingJointIssued (originalScroll)
open private seat panel views observed from YM.Integration.WilsonSeparatedPrefixMovingPhasePupil
open WilsonSeparatedPrefixMovingJointFiledPages (cash)
open WilsonSeparatedPrefixMovingJointOlderBook (accepted)
open WilsonSeparatedPrefixMovingJetService (actual)
variable {C:Credit}{e k j b older N:ℕ}
open WilsonSeparatedPrefixMovingJointExpansion (coin coefficient)
open WilsonSeparatedPrefixMovingJointSpectrum (physical)
open WilsonSeparatedPrefixMovingJointWaves (wave)
def row (S:𝓢(Euclid,ℂ))(φ:Rarity D)(p:CellR→Point4)(fire:Bool→CellR×Euclid→ℝ)(w:CellR×Euclid):ℝ:=
  ∑c:Bool,∑d:Bool,cash φ S w.2 (p w.1) c d*fire d w
theorem duty (S:𝓢(Euclid,ℂ))(φ:Rarity D)(p:CellR→Point4)(hp:Continuous p)(c d:Bool):
    Continuous fun w:CellR×Euclid=>cash φ S w.2 (p w.1) c d:=by
  have scout:Continuous fun w:CellR×Euclid=>coefficient (S w.2) c d:=by
    have hS:=S.continuous.comp (continuous_snd (X:=CellR))
    cases c <;> cases d <;> first | exact Complex.continuous_re.comp hS | exact Complex.continuous_im.comp hS |
      exact (Complex.continuous_im.comp hS).neg
  have arg:Continuous fun w:CellR×Euclid=>angle w.2 (p w.1):=by
    change Continuous fun w:CellR×Euclid=>(2*Real.pi)*inner ℝ w.2 (physical.symm (p w.1))
    exact continuous_const.mul (continuous_snd.inner (physical.symm.continuous.comp (hp.comp continuous_fst)))
  exact scout.mul (((scribble φ.ψ le_rfl).continuous.comp (hp.comp continuous_fst)).mul
    ((WilsonSeparatedPrefixMovingJointWaves.smooth c).continuous.comp arg))
theorem original (S:𝓢(Euclid,ℂ))(spectrum:∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖))
    (φ:Rarity D)(p:CellR→Point4)(hp:Continuous p)(fire:Bool→CellR×Euclid→ℝ)(m:ℕ)
    (priced:∀d,Continuous (fire d) ∧ ∃A:ℝ,0≤A ∧ ∀w:CellR×Euclid,‖fire d w‖≤A*(1+‖w.2‖^m)):
    let F:=row S φ p fire
    Integrable F (dayMeasure.prod volume) ∧
    (∫z,∫ξ,F (z,ξ) ∂volume ∂dayMeasure)=∫ξ,∫z,F (z,ξ) ∂dayMeasure ∂volume:=by
  intro F
  let localφ:C(CellR,ℝ):=⟨fun z=>φ.ψ.val (p z),(scribble φ.ψ le_rfl).continuous.comp hp⟩
  have waveLe (c:Bool)(t:ℝ):‖wave c t‖≤1:=by
    cases c <;> simp only [WilsonSeparatedPrefixMovingJointWaves.wave,Real.norm_eq_abs] <;> first | exact Real.abs_cos_le_one _ | exact Real.abs_sin_le_one _
  have coinLe (w:CellR×Euclid)(c d:Bool):‖cash φ S w.2 (p w.1) c d‖≤‖S w.2‖*‖localφ‖:=by
    change ‖coefficient (S w.2) c d*(localφ w.1*wave c (angle w.2 (p w.1)))‖≤_
    rw [norm_mul,norm_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using coin (S w.2) c d)
      ((mul_le_mul (localφ.norm_coe_le_norm w.1) (waveLe _ _) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have each (c d:Bool):Integrable (fun w:CellR×Euclid=>cash φ S w.2 (p w.1) c d*fire d w) (dayMeasure.prod volume):=by
    obtain ⟨cont,A,apos,fee⟩:=priced d
    have bound:=((spectrum m).comp_snd dayMeasure).const_mul (‖localφ‖*A)
    apply bound.mono' ((duty S φ p hp c d).mul cont).aestronglyMeasurable
    filter_upwards with w
    change ‖cash φ S w.2 (p w.1) c d*fire d w‖≤_
    rw [norm_mul]
    calc _≤(‖S w.2‖*‖localφ‖)*(A*(1+‖w.2‖^m)):=
           mul_le_mul (coinLe w c d) (fee w) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
         _ = _ := by change _=(‖localφ‖*A)*((1+‖w.2‖^m)*‖S w.2‖);ring
  have payable:Integrable F (dayMeasure.prod volume):=
    integrable_finsetSum Finset.univ fun c _=>integrable_finsetSum Finset.univ fun d _=>each c d
  exact ⟨payable,integral_integral_swap (f:=fun z ξ=>F (z,ξ)) payable⟩
end YM.Integration.WilsonSeparatedPrefixMovingJointChamberFubini
