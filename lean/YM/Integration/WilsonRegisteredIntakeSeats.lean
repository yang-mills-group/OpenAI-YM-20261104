import YM.Integration.WilsonRegisteredIntakeNorm

/-! A true previously registered complex mark can be added to the actual
perturbative carrier even when the two stage budgets record different
derivative orders. Every member of the prior team remains present. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredIntakeSeats
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
    ∃fees:ℕ→ℝ, SumBudget (fun i=>P.p.mass (Z.support i) (fees i)) cap ∧
      (s≤P.p.supportExponent → SumBudget (fun i=>Q.p.mass (Z.support i) (fees i)) cap) ∧
      (∀i,0≤fees i) ∧ ∀(i:ℕ)(χ:ℂ→L[ℝ]ℝ), (∀z,|χ z|≤‖z‖) →
      ∀old:Team (QLocalInheritedRegularSlots.carrier Q),
        ∃(W:Team (QLocalInheritedRegularSlots.carrier Q))(b:Leaf (QLocalInheritedRegularSlots.carrier Q)),
          W.own=insert b old.own ∧ b∉old.own ∧ W.weight=old.weight*fees i ∧ b.crest=Z.support i ∧
          ∀U,b.ingredient U=χ (Z.maskedTerm P i U):=by
  intro P Z L cap
  have norms:=WilsonRegisteredIntakeNorm.dated R (per:=per) live onset Q.p record
  obtain ⟨threshold,cover,order,power⟩:=norms
  have selected:=WilsonTranslatedFactory.based R.makes ref live o ((R.family.factory d N per).terminal.symm v)
  have good:Z.Format o R.family.params P:=selected.1
  obtain ⟨a,c,_,c0,total,_,⟨e,charged,legit⟩,_⟩:=selected.2
  have bill:SumBudget (fun i=>P.p.mass (Z.support i) (e i)) cap:=
    ⟨charged.1,charged.2.1,charged.2.2.trans ((le_add_of_nonneg_right c0).trans total)⟩
  refine ⟨e,bill,?_,fun i=>(legit i).1,?_⟩
  · intro reserve
    apply budget_mono bill
    · intro i;exact mul_nonneg (Real.exp_pos _).le (legit i).1
    · intro i
      unfold BudgetPoint.mass
      rw [cover,record.reserve]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right reserve (by positivity))) (legit i).1
  · intro i χ contract old
    let address:RegularAddress (R.family.side k per):=⟨o,Z.support i,good.origin i⟩
    have price:P.p.supBounds address.site address.support (Z.regular i) (e i):=legit i
    obtain ⟨smooth,money⟩:=WilsonRegisteredIntakeNorm.restrict threshold order power (good.smooth i) price
    obtain ⟨tag,unused⟩:=room Q address old
    let landed:=fun U=>χ (Z.regular i U)
    have legible:=WilsonCoherentMayerOldProjection.regular Q address (Z.regular i) χ smooth
    have budget:=WilsonCoherentMayerOldProjection.price Q address (Z.regular i) χ contract smooth money
    let W:=booked Q address old tag unused landed legible budget
    let b:=ManuscriptQLocalOrdinaryLeaf.leaf Q address landed legible budget tag
    have result:=entered Q address old tag unused landed legible budget
    refine ⟨W,b,rfl,fun h=>unused b h rfl,result.2.2.1,result.2.2.2.1,fun U=>?_⟩
    rw [result.2.2.2.2 U]
    change masked Q.p.threshold (Z.support i) (fun V=>χ (Z.regular i V)) U =
      χ (masked P.p.threshold (Z.support i) (Z.regular i) U)
    rw [threshold]
    by_cases healthy:Healthy P.p.threshold (Z.support i) U
    · rw [masked_eq _ _ _ _ healthy,masked_eq _ _ _ _ healthy]
    · rw [masked_ne _ _ _ _ healthy,masked_ne _ _ _ _ healthy,map_zero]

end YM.Integration.WilsonRegisteredIntakeSeats
