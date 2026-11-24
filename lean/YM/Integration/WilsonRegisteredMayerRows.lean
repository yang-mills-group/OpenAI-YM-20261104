import YM.Integration.WilsonCoherentMayerOldProjection
import YM.Integration.WilsonRegisteredAxialMass

/-! Original translated regular rows enter a previous marked team at their
own sites with their original common summable invoice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredMayerRows
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

theorem issued {k N per d:ℕ} (live:k≤N) (ref:R.family.ref d≤k) (v:R.family.label d)
    (o:Site (R.family.side k per)):
    let P:=R.family.path.rep N per k
    let Z:=packet R.makes live v o
    let L:=R.family.labels.level d
    ∃ (fees:ℕ→ℝ),
      SumBudget (fun i=>P.p.mass (Z.support i) (fees i)) ((R.family.path.levels.params k).columns*L.coeffSize (L.core Z.x)) ∧
      (∀i,0≤fees i) ∧ ∀(i:ℕ)(χ:ℂ→L[ℝ]ℝ), (∀z,|χ z|≤‖z‖) →
      ∀old:Team (QLocalInheritedRegularSlots.carrier P),
        ∃(W:Team (QLocalInheritedRegularSlots.carrier P))(b:Leaf (QLocalInheritedRegularSlots.carrier P)),
          old.own⊆W.own ∧ b∈W.own ∧ W.weight=old.weight*fees i ∧ b.crest=Z.support i ∧
            ∀U,b.ingredient U=χ (Z.maskedTerm P i U):=by
  intro P Z L
  have selected:=WilsonTranslatedFactory.based R.makes ref live o ((R.family.factory d N per).terminal.symm v)
  have good:Z.Format o R.family.params P:=selected.1
  obtain ⟨a,c,_,c0,total,_,⟨e,charged,legit⟩,_⟩:=selected.2
  refine ⟨e,⟨charged.1,charged.2.1,charged.2.2.trans ((le_add_of_nonneg_right c0).trans total)⟩,fun i=>(legit i).1,?_⟩
  intro i χ contract old
  let address:RegularAddress (R.family.side k per):=⟨o,Z.support i,good.origin i⟩
  have income:P.p.supBounds address.site address.support (Z.regular i) (e i):=legit i
  obtain ⟨W,b,prior,member,weight,support,reading⟩:=
    WilsonCoherentMayerOldProjection.seated P address (Z.regular i) χ contract (good.smooth i) income old
  refine ⟨W,b,prior,member,weight,support,fun U=>?_⟩
  rw [reading]
  change masked P.p.threshold (Z.support i) (fun V=>χ (Z.regular i V)) U = χ (masked P.p.threshold (Z.support i) (Z.regular i) U)
  by_cases healthy:Healthy P.p.threshold (Z.support i) U
  · rw [masked_eq _ _ _ _ healthy]
    rw [masked_eq _ _ _ _ healthy]
  · rw [masked_ne _ _ _ _ healthy]
    rw [masked_ne _ _ _ _ healthy,map_zero]

end YM.Integration.WilsonRegisteredMayerRows
