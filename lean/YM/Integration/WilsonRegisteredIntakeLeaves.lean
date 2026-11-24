import YM.Integration.WilsonRegisteredIntakeSeats

/-! An uncontracted finite choice of registered positions has one measurable
old source fee for each physical address. These fees precede the quadratures. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredIntakeLeaves
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical


open WilsonCoherentMayerOldSlots AnalyticBridge.VerifiedReset

open PhysicalNext.Repeat.Legato WilsonInheritedRegisteredField
variable {G:Gauge} (R:Run G)



theorem issued {k N per d f p:ℕ} {s:ℝ} (live:k≤N) (ref:R.family.ref d≤k)
    (onset:R.family.ref (max f p)≤k) (Q:Rep G (R.family.side k per))
    (record:LocalComparison.NormAt R.family k Q.p f p s)
    (v:R.family.label d) (o:Site (R.family.side k per)):
    let P:=R.family.path.rep N per k
    let Z:=packet R.makes live v o
    let L:=R.family.labels.level d
    let cap:=(R.family.path.levels.params k).columns*L.coeffSize (L.core Z.x)
    ∃e:ℕ→ℝ, SumBudget (fun i=>P.p.mass (Z.support i) (e i)) cap ∧
      (s≤P.p.supportExponent → SumBudget (fun i=>Q.p.mass (Z.support i) (e i)) cap) ∧
      ∀(i:ℕ)(χ:ℂ→L[ℝ]ℝ), (∀z,|χ z|≤‖z‖) →
      ∃b:Leaf (QLocalInheritedRegularSlots.carrier Q),b.weight=e i ∧ b.crest=Z.support i ∧
        o∈b.crest ∧ ∀U,b.ingredient U=χ (Z.maskedTerm P i U):=by
  intro P Z L cap
  obtain ⟨e,bill,submitted,_,seats⟩:=WilsonRegisteredIntakeSeats.issued R live ref onset Q record v o
  refine ⟨e,bill,submitted,?_⟩
  intro i χ contract
  let empty:Team (QLocalInheritedRegularSlots.carrier Q):=⟨∅,by simp⟩
  obtain ⟨W,b,one,unused,price,site,read⟩:=seats i χ contract empty
  have weight:b.weight=e i:=by
    change (∏b∈W.own,b.weight)=(∏b∈empty.own,b.weight)*e i at price
    simpa only [one,Finset.prod_insert unused,empty,Finset.prod_empty,mul_one,one_mul] using price
  have good:Z.Format o R.family.params P:=(WilsonTranslatedFactory.based R.makes ref live o
    ((R.family.factory d N per).terminal.symm v)).1
  exact ⟨b,weight,site,site.symm ▸ good.origin i,read⟩

end YM.Integration.WilsonRegisteredIntakeLeaves
