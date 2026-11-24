import YM.Integration.WilsonSeparatedPrefixMovingPhaseSource

/-! The actual normalized finite exterior equals its small returned source
plus a finite set of enrolled compact derivative words at the common center. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPhasePupil
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical ContDiff
open WilsonCoeffUV.Layout
open WilsonSeparatedPrefixMovingExteriorRemainder (remainder)
open WilsonSeparatedPrefixMovingProfileDerivatives (cut)
open WilsonSeparatedPrefixMovingCenterMoments (monomial)
open WilsonIndependentMatchedCoverProfile (word)
variable {D:ℕ}{G:Gauge}
private def seat (P:TowerS G D)(b:Cover):Volume D→ₗ[ℝ]Era G ℝ where
  toFun:=fun v=>shifted (tuftV (ContinuousLinearMap.apply ℝ ℝ v) P) b
  map_add':=by
    intro x y;apply Prod.ext
    · funext n i j w;change P.1 n i j _ (x+y)=P.1 n i j _ x+P.1 n i j _ y;exact map_add _ _ _
    funext i j w;change P.2 i j _ (x+y)=P.2 i j _ x+P.2 i j _ y;exact map_add _ _ _
  map_smul':=by
    intro a x;apply Prod.ext
    · funext n i j w;change P.1 n i j _ (a • x)=a • P.1 n i j _ x;exact map_smul _ _ _
    funext i j w;change P.2 i j _ (a • x)=a • P.2 i j _ x;exact map_smul _ _ _
private def panel (P:TowerS G D)(S:Finset Cover)(h:ℕ)(ε:ℝ):(Cover→Volume D)→ₗ[ℝ]Era G ℝ:=
  ∑b∈S,drumB h ε • (seat P b).comp (LinearMap.proj b)
private def views (φ:Rarity D)(ε y:ℝ)(o:CellR):Cover→Volume D:=fun b=>wheelC ε y b φ.ψ o
private theorem observed (P:TowerS G D)(φ:Rarity D)(ε y:ℝ)(hx:0<ε)(o:CellR)(S:Finset Cover)
    (contains:VisitsT φ ε y o⊆S)(h:ℕ):word P φ ε y o h=panel P S h ε (views φ ε y o):=by
  rw [word,pupil_eye _ _ _ _ _ _ hx]
  simp only [panel,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.proj_apply]
  refine Finset.sum_subset contains ?_
  intro i _ gone
  change drumB h ε • locale o (shoe P φ ε y i)=0
  rw [singless P ε y i o φ hx gone,smul_zero]
theorem original (P:TowerS G D)(φ:Rarity D)(hf:ContDiff ℝ ∞ φ.ψ.val)(ε y:ℝ)(hx:0<ε)
    (z o:CellR)(L h:ℕ):
    word P φ ε y z h=word P (remainder φ hf y z o L) ε y o h+
      ∑n∈Finset.range (L+1),((n.factorial:ℝ)⁻¹*(-y)^n) •
        ∑w:Fin n→Axis,monomial o w z • word P (cut φ hf w) ε y o h:=by
  classical
  let ψ:=remainder φ hf y z o L
  let seats (n:ℕ):Finset Cover:=Finset.univ.biUnion fun w:Fin n→Axis=>VisitsT (cut φ hf w) ε y o
  let S:=VisitsT φ ε y z ∪ VisitsT ψ ε y o ∪ (Finset.range (L+1)).biUnion seats
  have φpaid:VisitsT φ ε y z⊆S:=fun i hi=>Finset.mem_union_left _ (Finset.mem_union_left _ hi)
  have ψpaid:VisitsT ψ ε y o⊆S:=fun i hi=>Finset.mem_union_left _ (Finset.mem_union_right _ hi)
  have cuts (n:ℕ)(hn:n∈Finset.range (L+1))(w:Fin n→Axis):VisitsT (cut φ hf w) ε y o⊆S:=by
    intro i hi;exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨n,hn,Finset.mem_biUnion.mpr ⟨w,Finset.mem_univ _,hi⟩⟩)
  have field:views φ ε y z=views ψ ε y o+∑n∈Finset.range (L+1),
      ((n.factorial:ℝ)⁻¹*(-y)^n) • ∑w:Fin n→Axis,monomial o w z • views (cut φ hf w) ε y o:=by
    funext b
    have paid:=WilsonSeparatedPrefixMovingExteriorRemainder.registered φ hf ε y b z o L
    simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply]
    change wheelC ε y b φ.ψ z=wheelC ε y b ψ.ψ o+WilsonSeparatedPrefixMovingExteriorVolume.printed φ hf ε y b z o L
    rw [←sub_eq_iff_eq_add];exact paid.symm
  rw [observed P φ ε y hx z S φpaid h,field,map_add,←observed P ψ ε y hx o S ψpaid h,map_sum]
  congr 1
  refine Finset.sum_congr rfl fun n hn=>?_
  rw [map_smul,map_sum]
  apply congr_arg (_ • ·)
  refine Finset.sum_congr rfl fun w _=>?_
  rw [map_smul,←observed P (cut φ hf w) ε y hx o S (cuts n hn w) h]
theorem appointed (Q:SealR G)(φ:Rarity Q.D)(hf:ContDiff ℝ ∞ φ.ψ.val)(A:Levels G)(C:ChartRatio G)
    (t i N:ℕ)(y:ℝ)(z o:CellR)(X:Q.Rider)(L:ℕ):
    locale z (Q.spins A C φ t i N y X)=locale o (Q.spins A C (remainder φ hf y z o L) t i N y X)+
      ∑n∈Finset.range (L+1),((n.factorial:ℝ)⁻¹*(-y)^n) •
        ∑w:Fin n→Axis,monomial o w z • locale o (Q.spins A C (cut φ hf w) t i N y X):=
  original _ φ hf _ y (pace_pos ..) z o L Q.h
end YM.Integration.WilsonSeparatedPrefixMovingPhasePupil
