import YM.Integration.WilsonSeparatedPrefixMovingJointIssued
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
namespace YM.Integration.WilsonSeparatedPrefixMovingJointFiledPages
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
def cash (φ:Rarity D)(S:𝓢(Euclid,ℂ))(ξ:Euclid)(p:Point4)(c d:Bool):ℝ:=
  coefficient (S ξ) c d*(sheet φ (angle ξ) c).ψ.val p
theorem shifted (φ:Rarity D)(ψ:Rarity E)(p:Point4)(hψ:ContDiff ℝ ∞ ψ.ψ.val):
    originalScroll φ ψ p hψ = φ.ψ.val p • (home ψ 1 one_pos p).ψ:=by
  apply Subtype.ext
  funext q
  change φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(zoom ψ 1).val (-p+q)
  simp [zoom_at,sub_eq_neg_add]
theorem stamped (φ:Rarity D)(χ:Rarity E)(S:𝓢(Euclid,ℂ))(p:Point4)(hχ:ContDiff ℝ ∞ χ.ψ.val)(ξ:Euclid):
    WilsonSeparatedPrefixMovingJointPages.scroll (fun a:Euclid×Point4=>painted φ χ S p a.1 a.2)
      (WilsonSeparatedPrefixMovingJointKernelRead.whole φ χ S p hχ) ξ E =
    ∑c:Bool,∑d:Bool,cash φ S ξ p c d • (sheet χ (angle ξ) d).ψ:=by
  apply Subtype.ext
  funext q
  change (∑c:Bool,∑d:Bool,ink φ χ S p c d ξ q) = _
  simp [cash,WilsonSeparatedPrefixMovingJointKernel.ink]
theorem declared (φ:Rarity D)(ψ χ:Rarity E)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (window:∀p q:Point4,φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))):
    ∃S:𝓢(Euclid,ℂ),S=WilsonSeparatedPrefixMovingJointSpectrum.transformed ψ hψ ∧ (∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖))∧
    ∀(p:Point4)(ε y:ℝ)(s:Cover)(o:CellR)(L:Vote E),
      let waves:=fun ξ=>∑c:Bool,∑d:Bool,cash φ S ξ p c d*L (wheelC ε y s (sheet χ (angle ξ) d).ψ o)
      Integrable waves ∧ φ.ψ.val p*L (wheelC ε y s (home ψ 1 one_pos p).ψ o)=∫ξ,waves ξ:=by
  obtain ⟨S,identity,income,appointed⟩:=WilsonSeparatedPrefixMovingJointIssued.declared φ ψ χ hψ hχ window
  refine ⟨S,identity,income,?_⟩
  intro p ε y s o L
  let read:Scroll E→ₗ[ℝ]ℝ:=L.toLinearMap.comp ((LinearMap.proj s).comp (WilsonSeparatedPrefixMovingJointWord.ink E ε y o))
  have native (f:Scroll E):L (wheelC ε y s f o)=read f:=rfl
  have right (ξ:Euclid): L (field (fun a:Euclid×Point4=>painted φ χ S p a.1 a.2)
        (WilsonSeparatedPrefixMovingJointKernelRead.whole φ χ S p hχ) ε y s o ξ E)=
      ∑c:Bool,∑d:Bool,cash φ S ξ p c d*L (wheelC ε y s (sheet χ (angle ξ) d).ψ o):=by
    change read _=_
    rw [stamped φ χ S p hχ ξ]
    simp only [map_sum,map_smul,smul_eq_mul,native]
  have left:L (wheelC ε y s (originalScroll φ ψ p hψ) o)=φ.ψ.val p*L (wheelC ε y s (home ψ 1 one_pos p).ψ o):=by
    simp only [native,shifted,map_smul,smul_eq_mul]
  obtain ⟨inc,ear⟩:=appointed p ε y s o L
  simp_rw [right] at inc ear
  exact ⟨inc,left.symm.trans ear⟩
theorem original (φ:Rarity D)(ψ χ:Rarity E)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (window:∀p q:Point4,φ.ψ.val p*ψ.ψ.val (q-p)=φ.ψ.val p*(χ.ψ.val q*ψ.ψ.val (q-p))):
    ∃S:𝓢(Euclid,ℂ),(∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖))∧
    ∀(p:Point4)(ε y:ℝ)(s:Cover)(o:CellR)(L:Vote E),
      let waves:=fun ξ=>∑c:Bool,∑d:Bool,cash φ S ξ p c d*L (wheelC ε y s (sheet χ (angle ξ) d).ψ o)
      Integrable waves ∧ φ.ψ.val p*L (wheelC ε y s (home ψ 1 one_pos p).ψ o)=∫ξ,waves ξ:=by
  obtain ⟨S,_,data⟩:=declared φ ψ χ hψ hχ window
  exact ⟨S,data⟩
end YM.Integration.WilsonSeparatedPrefixMovingJointFiledPages
