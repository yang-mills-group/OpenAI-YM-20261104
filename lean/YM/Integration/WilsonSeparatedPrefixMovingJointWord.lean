import YM.Integration.WilsonSeparatedPrefixMovingJointAddress
import YM.Integration.WilsonSeparatedPrefixMovingPhasePupil

/-! Consume a separated two-profile expansion before the true pupil is joined to the near field. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointWord
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonCoeffUV.Layout
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
variable {G:Gauge}{D:ℕ}



open private panel views observed from YM.Integration.WilsonSeparatedPrefixMovingPhasePupil
open private look from YM.Integration.WilsonSeparatedPrefixMovingExteriorRemainder
open WilsonSeparatedPrefixMovingJointAddress (move)
universe u
variable {I:Type u}
def ink (D:ℕ)(ε y:ℝ)(o:CellR):Scroll D→ₗ[ℝ](Cover→Volume D):=
  LinearMap.pi fun s=>(page D).comp (look ε y s o)
theorem linear (P:TowerS G D)(F:Rarity D)(family:I→Rarity D)(S:Finset I)(c:I→ℝ)(v:ℝ)
    (profile:v • F.ψ=∑i∈S,c i • (family i).ψ)(ε y:ℝ)(hx:0<ε)(o:CellR)(h:ℕ):
    v • word P F ε y o h=∑i∈S,c i • word P (family i) ε y o h:=by
  classical
  let visits:=VisitsT F ε y o ∪ S.biUnion fun i=>VisitsT (family i) ε y o
  have covered:VisitsT F ε y o⊆visits:=Finset.subset_union_left
  have each (i:I)(hi:i∈S):VisitsT (family i) ε y o⊆visits:=
    (Finset.subset_biUnion_of_mem (fun i=>VisitsT (family i) ε y o) hi).trans Finset.subset_union_right
  let test:Scroll D→ₗ[ℝ]Era G ℝ:=(panel P visits h ε).comp (ink D ε y o)
  have native (A:Rarity D)(bought:VisitsT A ε y o⊆visits):word P A ε y o h=test A.ψ:=
    observed P A ε y hx o visits bought h
  rw [native F covered,←map_smul,profile,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul,native _ (each i hi)]
theorem actual (Q:SealR G)(A:Levels G)(C:ChartRatio G)(F:Rarity Q.D)(far:I→Rarity Q.D)
    (S:Finset I)(c:I→ℝ)(h:I→Point4→ℝ)(g:Point4→ℝ)(t b N:ℕ)(x v:ℝ)(hx:x≠0)
    (s:Cover)(o z:CellR)(X:Q.Rider)
    (registered:∀p:Point4,g p • (home F 1 one_pos ((paceT A.S t b/x) • p)).ψ=
        ∑i∈S,(c i*h i p) • (far i).ψ):
    let ε:=paceT A.S t b
    let p:=Mer.address x v o s z.val
    g p • move s (locale z (Q.spins A C F t b N ε X))=
      ∑i∈S,(c i*h i p) • locale o (Q.spins A C (far i) t b N (ε*v/x) X):=by
  intro ε p
  rw [WilsonSeparatedPrefixMovingJointAddress.appointed Q A C F t b N ε (ε*v/x) s z o X]
  have source:=registered p
  rw [←WilsonSeparatedPrefixMovingJointAddress.ratio ε x v hx s z o] at source
  exact linear _ _ far S _ _ source ε (ε*v/x) (pace_pos ..) o Q.h
end YM.Integration.WilsonSeparatedPrefixMovingJointWord
