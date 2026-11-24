import YM.Integration.WilsonOriginalSignedReceivedForest
import YM.Integration.LocalComparisonUniformModelPrice
import YM.Integration.ActualNormalizedLocalDensity

/-! Separate the true older ordinary and compulsory marked inputs before
the signed aperture integral. The ordinary term uses the positive selected
trajectory even when the independently carried vacuum has been rebooked. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReceivedMarkedCofactor
open Function Filter Finset MeasureTheory Lattice RG Wilson Precision Marker Multi Exterior Tree
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric PhysicalNext.Repeat.Legato Comparison.RG02 Integral
open Actual Order Push.SectorMeasure UniformPolynomialComparison
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {Γ : Census ι}
    (R : Run G) {J : Request ι} {A : NumericSchedule R.family J}
    (d : LocalFormal.Datum R.family Γ) {H : AnalyticInput J A d} {η : ℝ}
    (I : FullPreparedInputAt H η) (x : IndependentTests J.tests)
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "X" => testInclusion J.tests x
local notation "W" => fun v => H.inputRadii v/H.kernelCosts v
local notation "M" => MarkedPackets.uniformModelCost J.inputPacketRankCap (Fintype.card ι) (A.admittedCost d.level)
local notation "a" => (Fintype.card ι:ℝ)*I.regularPrice
local notation "D" => I.prepared.remainder.leaf (X)
local notation "Fine" => Config G (R.family.side (d.level+1) d.period)

def model (U : Fine) := Poly.pass (H.packets.read (X) (g) U)
def regular (U : Fine) := model R d (H:=H) x U * (Poly.pass ((D).log U)-1)
def carried (U : Fine) := model R d (H:=H) x U * Poly.pass ((D).log U)
def compulsory (U : Fine) := model R d (H:=H) x U * forcedNumerator (D) U

/-- Both signs and the complete analytic cofactor survive in every older
sector. The unmarked discrepancy is multiplied by the true old regular
packet. Every forced and mixed sector remains at its original field. -/
theorem split (U : Fine) :
    (I.input.leaf (X)).density U-ManuscriptQLocalActualLog.source R d H (X) U =
      ((P).eval U:ℂ) • regular R d I x U +
      ((I.carrier.rep.eval U:ℂ)-((P).eval U:ℂ)) • carried R d I x U +
      compulsory R d I x U := by
  rw [ManuscriptQLocalActualLog.inherited R d H (X) I U]
  simp only [regular, carried, compulsory, model, forcedNumerator_eq_difference, Handoff.legacyCarrier, mul_sub,
    mul_smul_comm, mul_one, smul_sub, sub_smul]
  abel

/-- Fixed-marker weighted cost at every field, including the compulsory
region, without a lower bound on the carried vacuum or its gas. -/
theorem price (U : Fine) :
    Poly.price (W) (regular R d I x U) ≤ M*(Real.exp (a)-1) ∧
    Poly.price (W) (carried R d I x U) ≤ M*Real.exp (a) := by
  let B := I.prepared.remainder_price
  have hw (v) : 0<(W) v := div_pos (H.input_radius_positive v) (H.kernel_positive v)
  obtain ⟨Q,hQ,hD,paid⟩ := B.physical_log_majorant H.kernel_positive x I.wellFormed.threshold
  have dominates {Z : IndependentTests J.tests × Fine → Poly Γ} {q : Poly Γ} (hq : Positive q)
      (hz : Dominates q Z) (z : IndependentTests J.tests × Fine) : Poly.price (W) (Z z) ≤ Poly.price (W) q := by
    apply Finset.sum_le_sum
    intro s _
    rw [hq.norm]
    exact mul_le_mul_of_nonneg_left (hz z s) (Poly.worth hw s).le
  have log : Poly.price (W) ((D).log U) ≤ a :=
    (dominates hQ hD (x,U)).trans paid
  have all : Poly.price (W) (Poly.pass ((D).log U)) ≤ Real.exp (a) :=
    (Poly.pass_budget hw _).trans (Real.exp_monotone log)
  have rem : Poly.price (W) (Poly.pass ((D).log U)-1) ≤ Real.exp (a)-1 := by
    rw [pass_eq_one_add_tail,add_sub_cancel_left]
    exact (dominates hQ.tail (hD.tail hQ) (x,U)).trans
      ((tail_price_le hQ hw).trans (sub_le_sub_right (Real.exp_monotone paid) 1))
  have m : Poly.price (W) (model R d (H:=H) x U) ≤ M :=
    H.input_paid.uniform_model J.inputPacketRankCap H.rank_bounded x U
  have mn : 0≤M := (Poly.nonnegative hw _).trans m
  constructor
  · exact (Poly.multiplication hw _ _).trans (mul_le_mul m rem (Poly.nonnegative hw _) mn)
  · exact (Poly.multiplication hw _ _).trans (mul_le_mul m all (Poly.nonnegative hw _) mn)

end YM.Integration.WilsonReceivedMarkedCofactor
