import YM.Integration.WilsonSeparatedPrefixMovingJointKernelRead
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
namespace YM.Integration.WilsonSeparatedPrefixMovingJointIssued
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
def originalScroll (φ:Rarity D)(ψ:Rarity E)(p:Point4)(hψ:ContDiff ℝ ∞ ψ.ψ.val):Scroll E:=
  ⟨fun q=>φ.ψ.val p*ψ.ψ.val (q-p),contDiff_infty.mp
    (contDiff_const.mul (hψ.comp (contDiff_id.sub contDiff_const))) E⟩
theorem declared (φ:Rarity D)(ψ χ:Rarity E)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (window:∀p q:Point4,φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))):
    ∃S:𝓢(Euclid,ℂ),S=WilsonSeparatedPrefixMovingJointSpectrum.transformed ψ hψ ∧ (∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖))∧
    ∀(p:Point4)(ε y:ℝ)(s:Cover)(o:CellR)(L:Vote E),
      let physical:=wheelC ε y s (originalScroll φ ψ p hψ) o
      let waves:=fun ξ=>field (fun a:Euclid×Point4=>painted φ χ S p a.1 a.2)
        (WilsonSeparatedPrefixMovingJointKernelRead.whole φ χ S p hχ) ε y s o ξ E
      Integrable (fun ξ=>L (waves ξ)) ∧ L physical=∫ξ,L (waves ξ):=by
  obtain ⟨S,identity,paid,page⟩:=WilsonSeparatedPrefixMovingJointKernelRead.declared φ ψ χ hψ hχ window
  refine ⟨S,identity,paid,?_⟩
  intro p ε y s o L
  let F:=fun a:Euclid×Point4=>painted φ χ S p a.1 a.2
  have hF:ContDiff ℝ ∞ F:=WilsonSeparatedPrefixMovingJointKernelRead.whole φ χ S p hχ
  have income (n:ℕ):∃b:Euclid→ℝ,Integrable b∧∀ξ q,‖iteratedFDeriv ℝ n (fun z=>F (ξ,z)) q‖≤b ξ:=by
    obtain ⟨B,_,bill⟩:=WilsonSeparatedPrefixMovingJointKernelRead.expense φ χ S p hχ n
    exact ⟨_,(paid n).const_mul B,bill⟩
  apply WilsonSeparatedPrefixMovingJointVote.original _ _ (WilsonSeparatedPrefixMovingJointPages.original F hF ε y s o E income) _ L
  intro i z
  let q:=WilsonCoeffUV.Mer.address ε y o s z.val
  let test:=ContinuousMultilinearMap.apply ℝ (fun _:Fin i.1.val=>Point4) ℝ (Embroider.dot ∘ i.2)
  change crease (sonal ε y o s (originalScroll φ ψ p hψ)) i.2 z.val = _
  rw [currentP ε y o s (originalScroll φ ψ p hψ) i.2 (Nat.le_of_lt_succ i.1.isLt)]
  change ε^i.1.val*test (iteratedFDeriv ℝ i.1.val (fun x=>φ.ψ.val p*ψ.ψ.val (x-p)) q)=_
  rw [(page p i.1.val q).2,←test.integral_comp_comm (page p i.1.val q).1,←integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun ξ=>(WilsonSeparatedPrefixMovingJointPages.native F hF ε y s o ξ i z).symm)
theorem original (φ:Rarity D)(ψ χ:Rarity E)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (window:∀p q:Point4,φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))):
    ∃S:𝓢(Euclid,ℂ),(∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖))∧
    ∀(p:Point4)(ε y:ℝ)(s:Cover)(o:CellR)(L:Vote E),
      let physical:=wheelC ε y s (originalScroll φ ψ p hψ) o
      let waves:=fun ξ=>field (fun a:Euclid×Point4=>painted φ χ S p a.1 a.2)
        (WilsonSeparatedPrefixMovingJointKernelRead.whole φ χ S p hχ) ε y s o ξ E
      Integrable (fun ξ=>L (waves ξ)) ∧ L physical=∫ξ,L (waves ξ):=by
  obtain ⟨S,_,data⟩:=declared φ ψ χ hψ hχ window
  exact ⟨S,data⟩
end YM.Integration.WilsonSeparatedPrefixMovingJointIssued
