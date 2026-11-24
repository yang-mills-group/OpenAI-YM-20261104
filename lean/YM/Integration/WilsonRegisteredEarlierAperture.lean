import YM.Integration.WilsonReceivedMarkedAperture
import YM.Integration.WilsonRegisteredIntakePair

/-! The original normalized Haar aperture pays the inherited ordinary
marked discrepancy also in the presence of the tested registered rows and
the entire earlier portfolio on a single field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredEarlierAperture
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

private theorem envelope : Leaf.All (fun y=>((P₁).eval y:ℂ) • (reg) y):=by
  let x₀ := testInclusion J.tests x
  have E := I.prepared.remainder_price.regular_error_envelope H.kernel_positive I.wellFormed.threshold x
  have B : Leaf.All (fun y=>Poly.pass ((I.prepared.remainder.leaf x₀).log y)-1) := by
    intro s
    obtain ⟨b,hb⟩ := E.cost
    exact ⟨(Poly.get s).continuous.measurable.comp E.meas,b,
      fun y => (norm_le_pi_norm (Poly.part _) s).trans (hb y)⟩
  have Z := Leaf.mul (ManuscriptQLocalActualLog.floor R d H x₀).safe B
  simpa only [WilsonReceivedMarkedCofactor.regular,WilsonReceivedMarkedCofactor.model,x₀,
    ManuscriptQLocalActualLog.literal,smul_mul_assoc] using Z


theorem tested (F : Forest (Δ).ratio) (A : (Δ).Choices→Set (F.Slice G))
    (closed:∀t,MeasurableSet (A t)) (V:Coarse) (D:Fine→ℂ) (meas:Measurable D)
    (c:ℝ) (cap:∀U,‖D U‖≤c):
    Poly.price (W) (((P₀).eval V:ℂ)⁻¹ • (∑t:(Δ).Choices,column F t (A t) (β) V
      (fun y=>((P₁).eval y:ℂ) • (D y • (reg) y))))≤c*(ξ):=by
  have charge:=Leaf.smul (show Envelope D from ⟨meas,c,cap⟩) (envelope R d I x)
  have ready:Leaf.All (fun y=>((P₁).eval y:ℂ) • (D y • (reg) y)):=by
    have same:(fun y=>((P₁).eval y:ℂ) • (D y • (reg) y)) =
        (fun y=>D y • (((P₁).eval y:ℂ) • (reg) y)):=funext fun y=>smul_comm _ _ _
    rw [same];exact charge
  have paid:=WilsonReceivedMarkedAperture.price R d F A closed V (W)
    (fun i=>div_pos (H.input_radius_positive i) (H.kernel_positive i)) (fun y=>D y • (reg) y) ready (c:=c*(ξ))
  have hw v:=div_pos (H.input_radius_positive v) (H.kernel_positive v)
  have bounded y:Poly.price (W) (D y • (reg) y)≤c*(ξ):=by
    rw [Poly.adapted]
    exact mul_le_mul (cap y) (WilsonReceivedMarkedCofactor.price R d I x y).1
      (Poly.nonnegative hw _) ((norm_nonneg _).trans (cap y))
  exact paid bounded

end YM.Integration.WilsonRegisteredEarlierAperture
