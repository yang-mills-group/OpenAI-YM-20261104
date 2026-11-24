import YM.Integration.WilsonSeparatedPrefixMovingJointChamberWord
import YM.Integration.WilsonSeparatedPrefixMovingJetSwap
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
namespace YM.Integration.WilsonSeparatedPrefixMovingJointContinuity
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
theorem arm (R:Realm G (e+1) C)(P:TowerS G D)(B:Era G ℝ)(hp:Auth k P)(hb:Auth j B)
    (ear:older≤b)(top:b≤N)(user:Era G ℝ→ₗ[ℝ]ℝ)(accept:WilsonSeparatedPrefixMovingJetPrice.eligible D user)
    (wide:WilsonSeparatedPrefixMovingJetService.eligible D user)(χ:Rarity D)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (ε y:ℝ)(pos:0<ε)(cap:ε≤1)(o:CellR)(h:ℕ)(d:Bool):
    Continuous fun ξ:Euclid=>user (cruises R.draws R.paid N (k+j) b older
      (agateV (word P (sheet χ (angle ξ) d) ε y o h) B)):=by
  have cont:=(WilsonSeparatedPrefixMovingJointChamberWord.original R P
    (tuftV WilsonSeparatedPrefixMovingCellFactor.constant B) hp (hb.tuft _) ear top user accept wide χ hχ ε y pos cap o h d).1.comp
    ((continuous_const (y:=zeroC)).prodMk (continuous_id (X:=Euclid)))
  change Continuous (fun ξ:Euclid=>user (cruises R.draws R.paid N (k+j) b older
    (agateV (word P (sheet χ (angle ξ) d) ε y o h) (locale zeroC (tuftV WilsonSeparatedPrefixMovingCellFactor.constant B))))) at cont
  simpa only [WilsonSeparatedPrefixMovingCellFactor.locus] using cont
theorem diagonal (f:Euclid→Euclid→ℝ)(f₁:∀η,Continuous fun ξ=>f ξ η)(f₂:∀ξ,Continuous (f ξ)):
    Measurable (Function.uncurry f) ∧ Measurable fun ξ=>f ξ ξ:=by
  have joint:Measurable (Function.uncurry f):=measurable_uncurry_of_continuous_of_measurable (u:=f) f₁ (fun ξ=>(f₂ ξ).measurable)
  exact ⟨joint,joint.comp (measurable_id.prodMk measurable_id : Measurable fun ξ:Euclid=>(ξ,ξ))⟩
theorem exchange (R:Realm G (e+1) C)(N b older:ℕ)(user:Era G ℝ→ₗ[ℝ]ℝ)
    {k j:ℕ}{A B:Era G ℝ}(ha:Auth k A)(hb:Auth j B):
    user (cruises R.draws R.paid N (j+k) b older (agateV B A))=
      user (cruises R.draws R.paid N (k+j) b older (agateV A B)):=by
  rw [Nat.add_comm j k,WilsonSeparatedPrefixMovingJetSwap.original hb ha]
set_option maxHeartbeats 3100000 in
theorem original (R:Realm G (e+1) C)(P:TowerS G D)(Q:TowerS G E)(hp:Auth k P)(hq:Auth j Q)
    (ear:older≤b)(top:b≤N)(user:Era G ℝ→ₗ[ℝ]ℝ)
    (p₁:WilsonSeparatedPrefixMovingJetPrice.eligible D user)(p₂:WilsonSeparatedPrefixMovingJetService.eligible D user)
    (q₁:WilsonSeparatedPrefixMovingJetPrice.eligible E user)(q₂:WilsonSeparatedPrefixMovingJetService.eligible E user)
    (φ:Rarity D)(χ:Rarity E)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (x y u v:ℝ)(xp:0<x)(xc:x≤1)(up:0<u)(uc:u≤1)(o z:CellR)(h l:ℕ)(c d:Bool):
    let a:=fun ξ=>word P (sheet φ (angle ξ) c) x y o h
    let b':=fun η=>word Q (sheet χ (angle η) d) u v z l
    let test:=fun ξ η:Euclid=>user (cruises R.draws R.paid N (k+j) b older (agateV (a ξ) (b' η)))
    Measurable (Function.uncurry test)∧Measurable fun ξ:Euclid=>test ξ ξ:=by
  intro a b' test
  have ha (ξ):Auth k (a ξ):=(placed h (sheet φ (angle ξ) c) (Auth_on hp) x y).tuft _
  have hb (η):Auth j (b' η):=(placed l (sheet χ (angle η) d) (Auth_on hq) u v).tuft _
  have first (η):Continuous (fun ξ=>test ξ η):=arm R P (b' η) hp (hb η) ear top user p₁ p₂ φ hφ x y xp xc o h c
  have second (ξ):Continuous (test ξ):=by
    have cont:=arm R Q (a ξ) hq (ha ξ) ear top user q₁ q₂ χ hχ u v up uc z l d
    let rev:=fun η:Euclid=>user (cruises R.draws R.paid N (j+k) b older (agateV (b' η) (a ξ)))
    have equality:rev=test ξ:=funext fun η=>exchange R N b older user (ha ξ) (hb η)
    exact equality ▸ (show Continuous rev from cont)
  exact diagonal test first second
end YM.Integration.WilsonSeparatedPrefixMovingJointContinuity
