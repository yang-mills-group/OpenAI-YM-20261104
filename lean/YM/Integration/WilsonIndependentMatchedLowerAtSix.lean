import YM.Integration.WilsonIndependentMatchedKernelResidual
import YM.WilsonCoeffUV.Stable.CostKme

/-! A lower stencil enters the same complete horizon-six fit as the upper
one, in raw horizon-six units. The printed signed address measures below
refer to the inherited source after the true inverse-square restoration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedLowerAtSix
open WilsonCoeffUV WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical


variable {G:Gauge}{D k u e:ℕ}{F:Labels.Frame G 6}{H:Hol G}{T:SectionData F}
  {p:6<D}{v:Rails 6 k u e}{E W K U:Credit}

def entered (L:Torch H T p v E W K)(L':ChorusLine H T p e E W U)(same:L'.arch=L.L)
    (m s N:ℕ)(live:L.L.V.anchor≤m)(top:m+s≤N)(P:TowerS G D)(ok:On k P)
    (A δ:ℝ)(positive:0≤A)(bill:∀j r:ℕ,j≤e→Fruit 0 1 u (P.2 j r) A) :
    CutsP H T p v E W K U :=
  WilsonIndependentMatchedKernelResidual.diagonal L L' same m s N live top
    (δ^2 • P) (ok.μ _) (δ^2*A) (mul_nonneg (sq_nonneg _) positive) (by
      intro j r hj
      have ink:=(show Award (P.2 j r) _ A from bill j r hj).μ (δ^2)
      rw [abs_of_nonneg (sq_nonneg δ)] at ink
      exact ink)

theorem priced (H:Hol G)(T:SectionData F)(p:6<D)(v:Rails 6 k u e)(E W K U:Credit) :
    ∃ C:Credit,∀ (L:Torch H T p v E W K)(L':ChorusLine H T p e E W U)
      (same:L'.arch=L.L)(m s N:ℕ)(live:L.L.V.anchor≤m)(top:m+s≤N)
      (P:TowerS G D)(ok:On k P)(A δ:ℝ)(positive:0≤A)(_:0<δ)
      (bill:∀j r:ℕ,j≤e→Fruit 0 1 u (P.2 j r) A),
      let X:=entered L L' same m s N live top P ok A δ positive bill
      X.springP X.i=δ^2 • P-Shrine X.Ntop X.tileP ∧
      (∀ i<X.i, Spout X.ax X.tx X.N (X.m+i) 6 k (X.springP (i+1))=X.springP i) ∧
      ∀ j≤e,∀ i≤X.i,∀ r, Keys_ ((δ^2)⁻¹ • (X.springP i).2 j r) 0 u
        ((3+(r:ℝ))^u * (C.buy X.Age *
          Real.exp (-(X.vesselsC.draws.S.scale X.ceilC -
            X.vesselsC.draws.S.scale (X.m+i))/4) * A)) := by
  obtain ⟨C,rate⟩:=WilsonIndependentMatchedKernelResidual.original H T p v E W K U
  refine ⟨C,?_⟩
  intro L L' same m s N live top P ok A δ positive hd bill
  let X:=entered L L' same m s N live top P ok A δ positive bill
  obtain ⟨issued,edge,cash⟩:=rate X
  refine ⟨issued,edge,?_⟩
  intro j hj i hi r
  apply certificate
  have restored:=(show Award ((X.springP i).2 j r) _ _ from cash j hj i hi r).μ ((δ^2)⁻¹)
  have fuel:X.fuel=δ^2*A:=rfl
  rw [fuel,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg δ))] at restored
  let z:= C.buy X.Age *
    Real.exp (-(X.vesselsC.draws.S.scale X.ceilC - X.vesselsC.draws.S.scale (X.m+i))/4)
  have cancel:(δ^2)⁻¹*(z*(δ^2*A))=z*A := by field_simp [ne_of_gt hd]
  change Award _ _ ((δ^2)⁻¹*(z*(δ^2*A))) at restored
  rw [cancel] at restored
  exact restored

end YM.Integration.WilsonIndependentMatchedLowerAtSix
end
