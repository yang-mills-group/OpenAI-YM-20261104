import YM.Integration.WilsonSeparatedPrefixMovingCenter
import YM.Integration.WilsonIndependentMatchedCoverProfile

/-! Numerical values of the actual printed near composite at its occupied
translated sites, with the source held on the original common cell. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingCenterPrint
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{n D j r:ℕ}{Q:Fin (n+1)→SealR G}
variable (A:Levels G)(C:ChartRatio G)(φ:Wilt Q)(X:Herit Q)(m b N:ℕ)
variable (F:Rarity D)(x y:ℝ)(o:CellR)

theorem cover (site:Cover)(w:Fin r→YForest G):
    (locale o (shoe (AutumnDay A C φ X m b N D) F x y site)).2 j r w=
      ∫ z:CellR,(shifted (LodeStar A C φ X m b N (paceT A.S m b)) site).2 j r w z*
        F.ψ.val (Mer.address x y o site z.val) ∂dayMeasure:=by
  exact hour_at dayMeasure _ (sonal x y o site F.ψ)

theorem finite (per:Side)(site:Cover)(w:Fin r→Woods G per):
    (locale o (shoe (AutumnDay A C φ X m b N D) F x y site)).1 per j r w=
      ∫ z:CellR,(shifted (LodeStar A C φ X m b N (paceT A.S m b)) site).1 per j r w z*
        F.ψ.val (Mer.address x y o site z.val) ∂dayMeasure:=by
  exact hour_at dayMeasure _ (sonal x y o site F.ψ)

theorem original (hx:0<x)(grade:ℕ)(w:Fin r→YForest G):
    (word (AutumnDay A C φ X m b N D) F x y o grade).2 j r w=
      ∑ site∈VisitsT F x y o,drumB grade x*
        ∫ z:CellR,(shifted (LodeStar A C φ X m b N (paceT A.S m b)) site).2 j r w z*
          F.ψ.val (Mer.address x y o site z.val) ∂dayMeasure:=by
  classical
  rw [word,pupil_eye _ _ _ _ _ _ hx]
  simp only [Prod.snd_sum,Finset.sum_apply,Prod.smul_snd,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro site _
  rw [cover]

theorem board (hx:0<x)(grade:ℕ)(per:Side)(w:Fin r→Woods G per):
    (word (AutumnDay A C φ X m b N D) F x y o grade).1 per j r w=
      ∑ site∈VisitsT F x y o,drumB grade x*
        ∫ z:CellR,(shifted (LodeStar A C φ X m b N (paceT A.S m b)) site).1 per j r w z*
          F.ψ.val (Mer.address x y o site z.val) ∂dayMeasure:=by
  classical
  rw [word,pupil_eye _ _ _ _ _ _ hx]
  simp only [Prod.fst_sum,Finset.sum_apply,Prod.smul_fst,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro site _
  rw [finite]

end YM.Integration.WilsonSeparatedPrefixMovingCenterPrint
