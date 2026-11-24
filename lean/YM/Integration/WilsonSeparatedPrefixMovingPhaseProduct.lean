import YM.Integration.WilsonSeparatedPrefixMovingPhasePupil
import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
import YM.Integration.WilsonIndependentFittedThermalProduct

/-! In one measured product, all retained exterior coefficients see their
genuine phase-weighted near field. The residual sees its own paid exterior. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPhaseProduct
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical ContDiff
open WilsonCoeffUV.Layout
open WilsonSeparatedPrefixMovingExteriorRemainder (remainder)
open WilsonSeparatedPrefixMovingProfileDerivatives (cut)
open WilsonSeparatedPrefixMovingCenterMoments (monomial paint)
open WilsonSeparatedPrefixMovingCellFactor (constant)
variable {G:Gauge}
def reading {V W:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]
    [NormedAddCommGroup W][NormedSpace ℝ W](L:V→L[ℝ]W):Era G V→ₗ[ℝ]Era G W where
  toFun:=tuftV L
  map_add':=by
    intro P Q;apply Prod.ext
    · funext n j r x;exact map_add L _ _
    funext j r x;exact map_add L _ _
  map_smul':=by
    intro t P;apply Prod.ext
    · funext n j r x;exact map_smul L _ _
    funext j r x;exact map_smul L _ _
private theorem scaleLeft {Z:Type*}(c:ℝ)(P Q:Pal ℝ Z):woad (c • P) Q=c • woad P Q:=by
  rw [←purePayment P c,WilsonIndependentFittedThermalProduct.left,purePayment]
def insert (B:Era G ℝ):Era G ℝ→ₗ[ℝ]Era G ℝ where
  toFun:=fun A=>agateV A B
  map_add':=fun A A'=>(WilsonIndependentMatchedTotalTop.binary A A' B).1
  map_smul':=fun c A=>Prod.ext (funext fun n=>scaleLeft c (A.1 n) (B.1 n)) (scaleLeft c A.2 B.2)
def group (y:ℝ)(L:ℕ)(o:CellR)(E:∀n:ℕ,(Fin n→Axis)→Era G ℝ)(B:Era G Lounge):Era G Lounge:=
  ∑n∈Finset.range (L+1),((n.factorial:ℝ)⁻¹*(-y)^n) • ∑w:Fin n→Axis,
    tuftV (paint (monomial o w)) (agateV (tuftV constant (E n w)) B)
def excess (y:ℝ)(L:ℕ)(o:CellR)(E:∀n:ℕ,(Fin n→Axis)→Era G ℝ)(A B:Era G Lounge):Era G Lounge:=
  agateV A B-group y L o E B
private theorem dyed (z:CellR)(weight:Lounge)(B:Era G Lounge):
    locale z (tuftV (paint weight) B)=weight z • locale z B:=rfl
theorem original (f:Lounge→L[ℝ]ℝ)(y:ℝ)(L:ℕ)(o:CellR)(E:∀n:ℕ,(Fin n→Axis)→Era G ℝ)(A B:Era G Lounge):
    tuftV f (agateV A B)=tuftV f (excess y L o E A B)+
      ∑n∈Finset.range (L+1),((n.factorial:ℝ)⁻¹*(-y)^n) • ∑w:Fin n→Axis,
        agateV (E n w) (tuftV (f.comp (paint (monomial o w))) B):=by
  have term (n:ℕ)(w:Fin n→Axis):reading f (tuftV (paint (monomial o w)) (agateV (tuftV constant (E n w)) B))
      =agateV (E n w) (tuftV (f.comp (paint (monomial o w))) B):=
    WilsonSeparatedPrefixMovingCellFactor.full (f.comp (paint (monomial o w))) (E n w) B
  change reading f _ = reading f (_-_) + _
  rw [map_sub,group]
  simp only [map_sum,map_smul,term,sub_add_cancel]
theorem sampled (y:ℝ)(L:ℕ)(z o:CellR)(E:∀n:ℕ,(Fin n→Axis)→Era G ℝ)(A B:Era G Lounge)(U:Era G ℝ)
    (fact:locale z A=U+∑n∈Finset.range (L+1),((n.factorial:ℝ)⁻¹*(-y)^n) • ∑w:Fin n→Axis,monomial o w z • E n w):
    locale z (excess y L o E A B)=agateV U (locale z B):=by
  have term (n:ℕ)(w:Fin n→Axis):reading (century z) (tuftV (paint (monomial o w)) (agateV (tuftV constant (E n w)) B))
      =monomial o w z • (insert (locale z B)) (E n w):=by
    change locale z _=_
    rw [dyed,woadChart,WilsonSeparatedPrefixMovingCellFactor.locus];rfl
  have heard:=congr_arg (insert (locale z B)) fact
  simp only [map_add,map_sum,map_smul] at heard
  change reading (century z) (_-group y L o E B)=_
  rw [map_sub]
  change locale z (agateV A B)-reading (century z) (group y L o E B)=_
  rw [woadChart,sub_eq_iff_eq_add,group]
  simp only [map_sum,map_smul,term]
  exact heard
theorem appointed (Q:SealR G)(A:Levels G)(C:ChartRatio G)(φ:Rarity Q.D)(hf:ContDiff ℝ ∞ φ.ψ.val)
    (t i N:ℕ)(y:ℝ)(z o:CellR)(X:Q.Rider)(B:Era G Lounge)(L:ℕ):
    let E:=fun (n:ℕ)(w:Fin n→Axis)=>locale o (Q.spins A C (cut φ hf w) t i N y X)
    locale z (excess y L o E (Q.spins A C φ t i N y X) B)=
      agateV (locale o (Q.spins A C (remainder φ hf y z o L) t i N y X)) (locale z B):=by
  intro E
  exact sampled y L z o E _ B _ (WilsonSeparatedPrefixMovingPhasePupil.appointed Q φ hf A C t i N y z o X L)
end YM.Integration.WilsonSeparatedPrefixMovingPhaseProduct
