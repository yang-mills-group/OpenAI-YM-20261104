import YM.Integration.WilsonInvariantActionMixedIntake
import YM.Integration.WilsonRegisteredPairAperture

/-! A normalized original tagged Haar receipt for the ordinary Q discrepancy
on the two actual rooted marks, preserving the entire funded earlier roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionMixedReceived
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
open WilsonInvariantActionMixedMaterial

def response (F:Forest (Δ).ratio) (A:(Δ).Choices→Set (F.Slice G)) (V:Coarse) (ψ:Fine→ℂ) :=
  (((P₀).eval V:ℂ)⁻¹ • (∑t:(Δ).Choices,column F t (A t) (β) V
    (fun y=>((P₁).eval y:ℂ) • (ψ y • (reg) y))))

theorem original (onset:R.family.ref (max J.inputFieldOrder J.inputDistanceOrder)≤d.level+1)
    (ref:R.family.ref 4≤d.level+1) (v w:R.family.label 4) (o₀ o₁:Site (R.family.side (d.level+1) d.period)):
    let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
    let Q:=ManuscriptQLocalVacuumFamily.source (QLocalInheritedPhysicalInlet.rep I) H.layers g 1
    let X:=packet R.makes d.below v o₀;let Z:=packet R.makes d.below w o₁
    let α:ℝ:=(R.family.S.a (d.level+1)^4)⁻¹
    let L:=R.family.labels.level 4
    let K:=(R.family.path.levels.params (d.level+1)).columns
    ∃e:ℕ→ℝ, SumBudget (fun i=>(P₁).p.mass (Z.support i) (e i)) (K*L.coeffSize (L.core Z.x)) ∧
      (J.inputSupport≤(P₁).p.supportExponent → SumBudget (fun i=>Q.p.mass (Z.support i) (e i)) (K*L.coeffSize (L.core Z.x))) ∧
      ∀(i:ℕ)(η χ:ℂ→L[ℝ]ℝ), (∀z,|χ z|≤‖z‖)→∀(old:Team (QLocalInheritedRegularSlots.carrier Q))
        (F:Forest (Δ).ratio) (A:(Δ).Choices→Set (F.Slice G)),(∀t,MeasurableSet (A t))→
      ∀(V:Coarse) (D:Fine→ℂ),Measurable D → ∀c:ℝ,(∀U,‖D U‖≤c) →
      let primal:=primary R.makes d.below v o₀
      let prior:=earlier R.makes d.below w o₁ ({i}:Set ℕ)
      let sample:=fun U=>D U*((η (primal U)*χ (prior U)*(∏l∈old.own,l.ingredient U):ℝ):ℂ)
      Poly.price (W) (response R d I x F A V sample)≤
        (c*α^2)*(WilsonCoherentMayerEntry.wallet R (L.core X.x) (P₁).p.threshold η*(old.weight*e i))*(ξ):=by
  intro g Q X Z α L K
  have norm:LocalComparison.NormAt R.family (d.level+1) Q.p
    J.inputFieldOrder J.inputDistanceOrder J.inputSupport:=U.input_norm d.level
  obtain ⟨e,bill,both,seats⟩:=WilsonInvariantActionMixedIntake.original R d.below ref onset Q norm v w o₀ o₁
  refine ⟨e,bill,both,?_⟩
  intro i η χ contract old F A closed V D borel c cap primal prior sample
  obtain ⟨roster,_,_,_,_,_,_,_,fund,seen⟩:=seats i η χ contract old
  let D':=fun y=>D y*(((α^2:ℝ):ℂ))
  have borel':Measurable D':=borel.mul_const _
  have cap' (y):‖D' y‖≤c*α^2:=by
    change ‖D y*(((α^2:ℝ):ℂ))‖≤_
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg α)]
    exact mul_le_mul_of_nonneg_right (cap y) (sq_nonneg α)
  have identity (y):D' y*((∏l∈roster.own,l.ingredient y:ℝ):ℂ)=sample y:=by
    have joined:= (seen y).2.2
    change (D y*↑(α^2))*↑(∏l∈roster.own,l.ingredient y)=D y*↑(η (primal y)*χ (prior y)*_)
    rw [mul_assoc,←Complex.ofReal_mul,joined]
  have price:=WilsonRegisteredPortfolioAperture.paid R d I x F A closed V roster D' borel' (c*α^2) cap'
  simpa only [response,identity,fund] using price

end YM.Integration.WilsonInvariantActionMixedReceived
