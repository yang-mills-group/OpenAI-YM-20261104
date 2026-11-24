import YM.Integration.WilsonMovingForkSharpGramArray
import YM.Integration.WilsonMovingForkSharpGramGrid
import YM.Integration.WilsonSeparatedPrefixMovingJointContinuity

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpGramWave
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonSeparatedPrefixMovingJointCell (toll)

open WilsonSeparatedPrefixMovingCellFactor (constant)
open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{H:Hol G}{n e h k D b m N older:ℕ}{C W V:Credit}

open WilsonSeparatedPrefixMovingJetBall (UnitJet)
variable {D j:ℕ}
variable {E:ℕ}
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonSeparatedPrefixMovingJointExpansion (angle)
open WilsonMovingForkSharpGramGrid (deposited site)
open WilsonSeparatedPrefixMovingJetService (size)
open WilsonSeparatedPrefixMovingJointFarBook (abroad)
open scoped ContDiff
def beam (R:Realm G (e+1) C)(P:TowerS G D)(Q:TowerS G E)(N k j b older i r:ℕ)(leg:Fin r→YForest G)
    (φ:Rarity D)(χ:Rarity E)(x y u v:ℝ)(o z:CellR)(h l:ℕ)(c d:Bool)(ξ:Euclid):ℝ:=
  deposited R N k j b older i r leg (word P (sheet φ (angle ξ) c) x y o h) (word Q (sheet χ (angle ξ) d) u v z l)
theorem original (R:Realm G (e+1) C){P:TowerS G D}{Q:TowerS G E}(hp:Auth k P)(hq:Auth j Q)
    (ear:older ≤ b)(top:b ≤ N)(i r:ℕ)(leg:Fin r→YForest G)(φ:Rarity D)(χ:Rarity E)
    (hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)(x y u v:ℝ)(xp:0<x)(xc:x ≤ 1)(up:0<u)(uc:u ≤ 1)
    (o z:CellR)(h l:ℕ)(c d:Bool):
    let F:=beam R P Q N k j b older i r leg φ χ x y u v o z h l c d
    Measurable F ∧ ∃M:ℝ,0 ≤ M ∧ ∀ξ,‖F ξ‖ ≤ M*(1+‖ξ‖^(D+E)):=by
  classical
  intro F
  refine ⟨(WilsonSeparatedPrefixMovingJointContinuity.original R P Q hp hq ear top (abroad i r leg)
    (WilsonSeparatedPrefixMovingJetPrice.cover _ _ _ _) (WilsonSeparatedPrefixMovingJetService.cover _ _ _ _)
    (WilsonSeparatedPrefixMovingJetPrice.cover _ _ _ _) (WilsonSeparatedPrefixMovingJetService.cover _ _ _ _)
    φ χ hφ hχ x y u v xp xc up uc o z h l c d).2,?_⟩
  let S:=canvasM φ x y
  let T:=canvasM χ u v
  let K:=fun s t=>‖(cruises R.draws R.paid N (k+j) b older
    (WilsonMovingForkSharpGramUnitBox.bank (shifted P s) (shifted Q t))).2 i r leg‖
  obtain ⟨a,ha,first⟩:=WilsonSeparatedPrefixMovingJointWavePages.original φ hφ
  obtain ⟨a',ha',second⟩:=WilsonSeparatedPrefixMovingJointWavePages.original χ hχ
  let cost:=fun s t=>(1+a)*(1+a')*K s t
  let M:=∑s∈S,‖drumB h x‖*∑t∈T,‖drumB l u‖*cost s t
  have ca:0 ≤ 1+a:=by linarith
  have ca':0 ≤ 1+a':=by linarith
  have cp (s t):0 ≤ cost s t:=mul_nonneg (mul_nonneg ca ca') (norm_nonneg _)
  have hM:0 ≤ M:=Finset.sum_nonneg fun s _=>mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun t _=>mul_nonneg (norm_nonneg _) (cp s t))
  refine ⟨M*4,by positivity,?_⟩
  intro ξ
  let φ':=sheet φ (angle ξ) c
  let χ':=sheet χ (angle ξ) d
  let U:=fun s=>wheelC x y s φ'.ψ o
  let V:=fun t=>wheelC u v t χ'.ψ z
  let L:=1+‖ξ‖^D
  let L':=1+‖ξ‖^E
  have oneL:1 ≤ L:=le_add_of_nonneg_right (pow_nonneg (norm_nonneg ξ) _)
  have oneL':1 ≤ L':=le_add_of_nonneg_right (pow_nonneg (norm_nonneg ξ) _)
  have paid (s):size (U s) ≤ (1+a)*L:=by
    have h₁:‖U s‖ ≤ a*L:=(first c x y s o xp.le xc).2 ξ
    exact max_le (by nlinarith) (by nlinarith)
  have paid' (t):size (V t) ≤ (1+a')*L':=by
    have h₁:‖V t‖ ≤ a'*L':=(second d u v t z up.le uc).2 ξ
    exact max_le (by nlinarith) (by nlinarith)
  let f:=fun s t=>deposited R N k j b older i r leg (site P φ' x y o s) (site Q χ' u v z t)
  have bound (s t):‖f s t‖ ≤ cost s t*(L*L'):=by
    have original:=WilsonMovingForkSharpGramAxisBox.original R (hp.shifted s) (hq.shifted t) ear top i r leg (U s) (V t)
    change ‖f s t‖ ≤ size (U s)*size (V t)*K s t at original
    have kpos:0 ≤ K s t:=norm_nonneg _
    refine original.trans ?_
    calc
      _ ≤ ((1+a)*L*((1+a')*L'))*K s t:=mul_le_mul_of_nonneg_right
        (mul_le_mul (paid s) (paid' t) (WilsonSeparatedPrefixMovingJetService.positive _).le (mul_nonneg ca (zero_le_one.trans oneL))) kpos
      _ = cost s t*(L*L'):=by unfold cost;ring
  have cut:F ξ=∑s∈S,drumB h x*∑t∈T,drumB l u*f s t:=
    WilsonMovingForkSharpGramGrid.original R hp hq ear top i r leg φ' χ' x y u v xp up o z S T
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) h l
  rw [cut]
  exact (WilsonMovingForkSharpGramArray.finite S T _ _ _ cost f bound).trans (calc
    M*(L*L') ≤ M*(4*(1+‖ξ‖^(D+E))):=mul_le_mul_of_nonneg_left
      (WilsonMovingForkSharpGramArray.growth ‖ξ‖ (norm_nonneg ξ) D E) hM
    _=M*4*(1+‖ξ‖^(D+E)):=by ring)

end YM.Integration.WilsonMovingForkSharpGramWave
