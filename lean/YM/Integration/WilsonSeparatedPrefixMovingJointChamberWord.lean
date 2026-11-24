import YM.Integration.WilsonSeparatedPrefixMovingJointOlderBook
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
namespace YM.Integration.WilsonSeparatedPrefixMovingJointChamberWord
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
theorem original (R:Realm G (e+1) C)(P:TowerS G E)(B:Era G Lounge)(hp:Auth k P)(hb:Auth j B)
    (ear:older≤b)(top:b≤N)(user:Era G ℝ→ₗ[ℝ]ℝ)(licensed:WilsonSeparatedPrefixMovingJetPrice.eligible E user)
    (wide:WilsonSeparatedPrefixMovingJetService.eligible E user)(χ:Rarity E)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (ε y:ℝ)(pos:0<ε)(cap:ε≤1)(o:CellR)(h:ℕ)(d:Bool):
    let run:=fun w:CellR×Euclid=>accepted R N k j b older (locale w.1 B) user P (sheet χ (angle w.2) d) ε y o h
    Continuous run ∧ ∃M:ℝ,0≤M ∧ ∀w:CellR×Euclid,‖run w‖≤M*(1+‖w.2‖^E):=by
  classical
  intro run
  let V:=canvasM χ ε y
  let pane:=fun s ξ=>wheelC ε y s (sheet χ (angle ξ) d).ψ o
  let row:=fun s (w:CellR×Euclid)=>actual R N k j b older (shifted P s) B user (w.1,pane s w.2)
  have written (w:CellR×Euclid):run w=∑s∈V,drumB h ε*row s w:=by
    obtain ⟨prior,received,_⟩:=WilsonSeparatedPrefixMovingJetOffice.original R (hb.tuft (century w.1)) ear top user hp licensed
    let F:=sheet χ (angle w.2) d
    have wt:Auth k (word P F ε y o h):=(placed h F (Auth_on hp) ε y).tuft _
    have atSite (s:Cover)(v:Volume E):prior (seat P s v)=actual R N k j b older (shifted P s) B user (w.1,v):=by
      rw [received (seat P s v) ((hp.tuft (ContinuousLinearMap.apply ℝ ℝ v)).shifted s)]
      rfl
    have old:run w=prior (word P F ε y o h):=(received _ wt).symm
    have contains:VisitsT F ε y o⊆V:=Finset.filter_subset _ _
    rw [old,observed P F ε y pos o V contains h]
    simp only [show panel P V h ε = ∑s∈V,drumB h ε • (seat P s).comp (LinearMap.proj s) from rfl,LinearMap.sum_apply,
      LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.proj_apply,map_sum,map_smul,smul_eq_mul,views,atSite]
    rfl
  obtain ⟨W,hW,wave⟩:=WilsonSeparatedPrefixMovingJointWavePages.original χ hχ
  have entries (s:Cover):Continuous (row s) ∧ ∃L:ℝ,0≤L ∧ ∀w:CellR×Euclid,‖row s w‖≤L*(1+‖w.2‖^E):=by
    obtain ⟨cont,M,Mpos,fare⟩:=WilsonSeparatedPrefixMovingJetService.original R (hp.shifted s) hb ear top user wide
    obtain ⟨varies,pay⟩:=wave d ε y s o pos.le cap
    refine ⟨cont.comp (continuous_fst.prodMk (varies.comp continuous_snd)),M*(1+W),by positivity,?_⟩
    intro w
    have pol:1≤1+‖w.2‖^E:=le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
    calc
      _≤M*WilsonSeparatedPrefixMovingJetService.size (pane s w.2):=fare w.1 _
      _≤M*((1+W)*(1+‖w.2‖^E)):=by
        apply mul_le_mul_of_nonneg_left _ Mpos
        apply max_le
        · calc 1≤1+‖w.2‖^E:=pol
               _≤(1+W)*(1+‖w.2‖^E):=le_mul_of_one_le_left (zero_le_one.trans pol) (by linarith)
        exact (pay w.2).trans (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans pol))
      _=(M*(1+W))*(1+‖w.2‖^E):=(mul_assoc _ _ _).symm
  choose L Lpos budget using fun s=>(entries s).2
  have full:Continuous fun w:CellR×Euclid=>∑s∈V,drumB h ε*row s w:=
    continuous_finsetSum V fun s _=>continuous_const.mul (entries s).1
  refine ⟨full.congr (fun w=>(written w).symm),∑s∈V,‖drumB h ε‖*L s,
    Finset.sum_nonneg fun s _=>mul_nonneg (norm_nonneg _) (Lpos s),?_⟩
  intro w
  rw [written,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s _
  rw [norm_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (budget s w) (norm_nonneg _)
end YM.Integration.WilsonSeparatedPrefixMovingJointChamberWord
