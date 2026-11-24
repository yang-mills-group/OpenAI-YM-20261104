import YM.Integration.WilsonRegisteredEarlierAperture

/-! Integrate arbitrary previously booked old and newly registered probes on
the same physical compact configuration, including its original positive
incumbent and any chosen admissible subset of each branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredPortfolioAperture
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

theorem paid (F:Forest (Δ).ratio) (A:(Δ).Choices→Set (F.Slice G))
    (closed:∀t,MeasurableSet (A t)) (V:Coarse) {Y:Rep G (R.family.side (d.level+1) d.period)}
    (team:Team Y) (D:Fine→ℂ) (meas:Measurable D) (c:ℝ) (cap:∀U,‖D U‖≤c):
    Poly.price (W) (((P₀).eval V:ℂ)⁻¹ • (∑t:(Δ).Choices,column F t (A t) (β) V
      (fun y=>((P₁).eval y:ℂ) •
        ((D y*((∏b∈team.own,b.ingredient y:ℝ):ℂ)) • (reg) y))))≤c*team.weight*(ξ):=by
  let probe (y:Fine):ℝ:=∏b∈team.own,b.ingredient y
  have borel:Measurable probe:=Finset.measurable_fun_prod _ fun z _=>z.borel
  have size (y:Fine):‖probe y‖≤team.weight:=by
    change ‖∏b∈team.own,b.ingredient y‖≤∏b∈team.own,b.weight
    rw [norm_prod]
    exact Finset.prod_le_prod (fun b _=>norm_nonneg _) (fun b _=>b.earn y)
  apply WilsonRegisteredEarlierAperture.tested R d I x F A closed V
    (fun y=>D y*(probe y:ℂ)) (meas.mul (Complex.measurable_ofReal.comp borel))
  intro y
  rw [norm_mul,Complex.norm_real]
  exact mul_le_mul (cap y) (size y) (norm_nonneg _) ((norm_nonneg _).trans (cap y))

end YM.Integration.WilsonRegisteredPortfolioAperture
