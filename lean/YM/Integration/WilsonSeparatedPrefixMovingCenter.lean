import YM.Integration.WilsonSeparatedPrefixMovingNearReturn
import YM.Integration.WilsonSeparatedPrefixMovingLenses

/-! Open the captured near field against the actual displaced exterior test.
Every cover site and all earlier scalar or higher-rank deposits stay in the
joint integral over the single original center cell. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingCenter
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical

variable {G:Gauge}{n D j r:ℕ}{Q:Fin (n+1)→SealR G}

/-- At every cover tensor coefficient the genuine encoded test supplied to
the captured response gives back its common center integral. -/
theorem read (A:Levels G)(C:ChartRatio G)(φ:Wilt Q)(X:Herit Q)(m b N:ℕ)
    (ψ:Phrase D)(s y:ℝ)(site:Cover)(o:CellR)(w:Fin r→YForest G):
    (AutumnDay A C φ X m b N D).2 j r w (wheelC s y site ψ o)=
      ∫ z:CellR,(LodeStar A C φ X m b N (paceT A.S m b)).2 j r w z*
        ψ.val (Mer.address s y o site z.val) ∂dayMeasure:=by
  exact hour_at dayMeasure _ (sonal s y o site ψ)

/-- The same formula evaluates a reflected test on the far ruler, with the
physical near and far sites still on one board. -/
theorem physical (A:Levels G)(C:ChartRatio G)(φ:Wilt Q)(X:Herit Q)(m b N:ℕ)
    (ψ:Phrase D)(s y T:ℝ)(tp:0<T)(site:Cover)(o:CellR)(w:Fin r→YForest G):
    (AutumnDay A C φ X m b N D).2 j r w (wheelC (s/T) (y/T) site ψ o)=
      ∫ z:CellR,(LodeStar A C φ X m b N (paceT A.S m b)).2 j r w z*
        ψ.val (T⁻¹ • Mer.address s y o site z.val) ∂dayMeasure:=by
  rw [read];congr 1;funext z
  have eq:=WilsonSeparatedPrefixMovingLenses.address_scale T s y o site z.val tp
  rw [←eq,inv_smul_smul₀ tp.ne']

end YM.Integration.WilsonSeparatedPrefixMovingCenter
