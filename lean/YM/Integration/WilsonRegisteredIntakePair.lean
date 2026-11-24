import YM.Integration.WilsonRegisteredIntakeSeats

/-! The two original measured source addresses are seated together on a single
chosen perturbative carrier. All earlier ordinary factors stay in the product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredIntakePair
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



theorem paired {k N per d₁ d₂ f p:ℕ} {s:ℝ} (live:k≤N)
    (ref₁:R.family.ref d₁≤k) (ref₂:R.family.ref d₂≤k) (onset:R.family.ref (max f p)≤k)
    (Q:Rep G (R.family.side k per)) (record:LocalComparison.NormAt R.family k Q.p f p s)
    (v₁:R.family.label d₁) (v₂:R.family.label d₂) (o₁ o₂:Site (R.family.side k per)):
    let P:=R.family.path.rep N per k
    let Z₁:=packet R.makes live v₁ o₁
    let Z₂:=packet R.makes live v₂ o₂
    let L₁:=R.family.labels.level d₁
    let L₂:=R.family.labels.level d₂
    let c:=(R.family.path.levels.params k).columns
    ∃e₁ e₂:ℕ→ℝ, SumBudget (fun i=>P.p.mass (Z₁.support i) (e₁ i)) (c*L₁.coeffSize (L₁.core Z₁.x)) ∧
      SumBudget (fun j=>P.p.mass (Z₂.support j) (e₂ j)) (c*L₂.coeffSize (L₂.core Z₂.x)) ∧
      (s≤P.p.supportExponent →
        SumBudget (fun i=>Q.p.mass (Z₁.support i) (e₁ i)) (c*L₁.coeffSize (L₁.core Z₁.x)) ∧
        SumBudget (fun j=>Q.p.mass (Z₂.support j) (e₂ j)) (c*L₂.coeffSize (L₂.core Z₂.x))) ∧
      ∀(i j:ℕ)(χ ψ:ℂ→L[ℝ]ℝ), (∀z,|χ z|≤‖z‖) → (∀z,|ψ z|≤‖z‖) →
      ∀old:Team (QLocalInheritedRegularSlots.carrier Q),
        ∃W:Team (QLocalInheritedRegularSlots.carrier Q),
          W.weight=(old.weight*e₁ i)*e₂ j ∧ old.own⊆W.own ∧
          ∀U,(∏b∈W.own,b.ingredient U)=
            χ (Z₁.maskedTerm P i U)*ψ (Z₂.maskedTerm P j U)*(∏b∈old.own,b.ingredient U):=by
  intro P Z₁ Z₂ L₁ L₂ c
  obtain ⟨e₁,bill₁,submitted₁,_,issued₁⟩:=WilsonRegisteredIntakeSeats.issued R live ref₁ onset Q record v₁ o₁
  obtain ⟨e₂,bill₂,submitted₂,_,issued₂⟩:=WilsonRegisteredIntakeSeats.issued R live ref₂ onset Q record v₂ o₂
  refine ⟨e₁,e₂,bill₁,bill₂,fun hs=>⟨submitted₁ hs,submitted₂ hs⟩,?_⟩
  intro i j χ ψ cχ cψ old
  obtain ⟨W₁,b₁,one,fresh₁,price₁,_,read₁⟩:=issued₁ i χ cχ old
  obtain ⟨W₂,b₂,two,fresh₂,price₂,_,read₂⟩:=issued₂ j ψ cψ W₁
  refine ⟨W₂,price₂.trans (congrArg (fun z=>z*e₂ j) price₁),?_,?_⟩
  · rw [two,one]
    exact (Finset.subset_insert ..).trans (Finset.subset_insert ..)
  · intro U
    rw [two,Finset.prod_insert fresh₂,one,Finset.prod_insert fresh₁,read₂,read₁]
    ring

end YM.Integration.WilsonRegisteredIntakePair
