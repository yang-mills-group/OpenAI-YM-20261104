import YM.Integration.WilsonRegisteredSectorIntake
import YM.Integration.WilsonRegisteredPortfolioAperture

/-! The genuine two-address Wilson source with any previous signed
portfolio is charged inside one true normalized, tagged forest integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredPairAperture
open Function Filter Finset MeasureTheory Lattice RG Wilson Precision Marker Multi Exterior Tree
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric PhysicalNext.Repeat.Legato Comparison.RG02 Integral
open Actual Order Push.SectorMeasure WilsonOriginalSignedForestAperture
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {Γ : Census ι}

variable (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "P₁" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "Fine" => Config G (R.family.side (d.level+1) d.period)
local notation "Coarse" => Config G (R.family.side d.level d.period)
set_option quotPrecheck false in
local notation "β" => (P₁).beta

variable {J : Request ι} {U : NumericSchedule R.family J} {H : AnalyticInput J U d}
    {η : ℝ} (I : FullPreparedInputAt H η) (x : IndependentTests J.tests)
local notation "W" => fun v => H.inputRadii v/H.kernelCosts v
local notation "M" => MarkedPackets.uniformModelCost J.inputPacketRankCap (Fintype.card ι) (U.admittedCost d.level)


open PhysicalNext.Repeat RGLocalTaylor.Insert
local notation "reg" => WilsonReceivedMarkedCofactor.regular R d I x
local notation "ξ" => M*(Real.exp ((Fintype.card ι:ℝ)*I.regularPrice)-1)


open RGLocalTaylor RG01.Survive PhysicalNext.Repeat.Lotus


open WilsonInheritedRegisteredField
theorem original (Q:Rep G (R.family.side (d.level+1) d.period))
    (issued:WilsonRegisteredHeightIntake.Bought R d Q)
    (d₁ d₂:ℕ)(ref₁:R.family.ref d₁≤d.level+1)(ref₂:R.family.ref d₂≤d.level+1)
    (v₁:R.family.label d₁)(v₂:R.family.label d₂)(o₁ o₂:Site (R.family.side (d.level+1) d.period)):
    let Z₁:=packet R.makes d.below v₁ o₁
    let Z₂:=packet R.makes d.below v₂ o₂
    let K:=(R.family.path.levels.params (d.level+1)).columns
    let L₁:=R.family.labels.level d₁
    let L₂:=R.family.labels.level d₂
    ∃e₁ e₂:ℕ→ℝ,
      SumBudget (fun i=>(P₁).p.mass (Z₁.support i) (e₁ i)) (K*L₁.coeffSize (L₁.core Z₁.x)) ∧
      SumBudget (fun j=>(P₁).p.mass (Z₂.support j) (e₂ j)) (K*L₂.coeffSize (L₂.core Z₂.x)) ∧
      ∀(i j:ℕ)(χ ψ:ℂ→L[ℝ]ℝ), (∀z,|χ z|≤‖z‖)→(∀z,|ψ z|≤‖z‖)→
      ∀(old:Team (QLocalInheritedRegularSlots.carrier Q))
        (F:Forest (Δ).ratio) (A:(Δ).Choices→Set (F.Slice G)),(∀t,MeasurableSet (A t))→
      ∀(V:Coarse) (D:Fine→ℂ),Measurable D → ∀c:ℝ,(∀U,‖D U‖≤c) →
      Poly.price (W) (((P₀).eval V:ℂ)⁻¹ • (∑t:(Δ).Choices,column F t (A t) (β) V
        (fun y=>((P₁).eval y:ℂ) •
          ((D y*((χ (Z₁.maskedTerm (P₁) i y)*ψ (Z₂.maskedTerm (P₁) j y)*
            ∏b∈old.own,b.ingredient y:ℝ):ℂ)) • (reg) y)))) ≤
              c*((old.weight*e₁ i)*e₂ j)*(ξ):=by
  intro Z₁ Z₂ K L₁ L₂
  obtain ⟨e₁,e₂,bill₁,bill₂,_,seats⟩:=issued d₁ d₂ ref₁ ref₂ v₁ v₂ o₁ o₂
  refine ⟨e₁,e₂,bill₁,bill₂,?_⟩
  intro i j χ ψ hχ hψ old F A closed V D borel c cap
  obtain ⟨team,budget,_,joined⟩:=seats i j χ ψ hχ hψ old
  have result:=WilsonRegisteredPortfolioAperture.paid R d I x F A closed V team D borel c cap
  simpa only [joined,budget] using result

end YM.Integration.WilsonRegisteredPairAperture
