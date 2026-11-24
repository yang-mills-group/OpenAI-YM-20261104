import YM.Integration.FullQLocalNumericSchedule
import YM.Integration.ActualRunAdmissionClock
import YM.Integration.ActualRunAdjacentHatBeta
import YM.WilsonCoeffUV.Marked.Paths.Purchase

/-! The bought original marked width fits every fixed requested support on
the same physical calendar, uniformly before cutoffs and root positions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedNativePacketGeometry
open Filter Lattice Wilson RG RG.Supply Precision Marker FullQLocal FullQLocal.RenderedStep
open PhysicalNext PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas
open scoped Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (R : Run G) (hG : G.Simple)

include hG in
theorem all_points (σ : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ p : BudgetPoint,
      p.B=R.family.path.levels.clock.coverSize m → p.supportExponent ≤ σ →
      p.supportExponent*(1+Real.log (Real.log (R.family.path.levels.clock.hatBeta m)))≤(p.B:ℝ)/4 := by
  let f := fun m=>Real.log (R.family.path.levels.clock.hatBeta m)
  have big : Tendsto f atTop atTop := Real.tendsto_log_atTop.comp (WardBin.bell R.family.path.levels hG)
  filter_upwards [big.eventually_ge_atTop (max 1 (4*σ))] with m hm
  intro p block sup
  have h₁ : 1≤f m := (le_max_left _ _).trans hm
  have h₄ : 4*σ≤f m := (le_max_right _ _).trans hm
  have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le h₁)
  have ceil : (f m)^2≤(p.B:ℝ) := by
    rw [block]
    exact Nat.le_ceil _
  have a := mul_le_mul_of_nonneg_left (show 1+Real.log (f m)≤f m by linarith) p.exponent_pos.le
  have b := mul_le_mul_of_nonneg_right (show 4*p.supportExponent≤f m by linarith)
    (zero_le_one.trans h₁)
  change p.supportExponent*(1+Real.log (f m))≤(p.B:ℝ)/4
  nlinarith only [a,b,ceil]

omit [DecidableEq V] [Fintype V] in
include hG in
theorem eventually (J : Request V) :
    ∀ᶠ m : ℕ in atTop, ∀ A : NumericSchedule R.family J,
      (A.outputNorm m).supportExponent*(1+Real.log (Real.log (R.family.path.levels.clock.hatBeta m)))≤
        ((A.outputNorm m).B:ℝ)/4 := by
  filter_upwards [all_points R hG J.outputSupport] with m hm
  intro A
  exact hm _ (A.output_norm m).block (A.output_norm m).reserve.le

theorem reserve (p : BudgetPoint) {width cost : ℝ} (hw : 0<width)
    (space : p.supportExponent*cost≤(p.B:ℝ)/4) (invoice : width⁻¹≤cost) :
    p.supportExponent/(p.B:ℝ)≤width/4 := by
  have h := (mul_le_mul_of_nonneg_left invoice p.exponent_pos.le).trans space
  have t := mul_le_mul_of_nonneg_right h hw.le
  rw [mul_assoc,inv_mul_cancel₀ hw.ne',mul_one] at t
  exact (div_le_iff₀ (Nat.cast_pos.mpr p.B_pos)).2 (by nlinarith only [t])

variable {e : ℕ} (J : Request V)

omit [DecidableEq V] [Fintype V] in
include hG in
theorem insured :
    ∀ᶠ m : ℕ in atTop, ∀ (A : NumericSchedule R.family J) (b k : ℕ)
      (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
      Q.y=zz R.family.path.levels → Insure b k Q Credit.leanC →
      0<VestS b k Q m hm ∧
        (A.outputNorm m).supportExponent/((A.outputNorm m).B:ℝ)≤VestS b k Q m hm/4 := by
  filter_upwards [eventually R hG J] with m h
  intro A b k Q hm hy sale
  have positive := (sale.proof m hm).affordable
  have pay := (sale.labor m hm).1
  change (VestS b k Q m hm)⁻¹≤Credit.leanC.buy (Q.y m) at pay
  rw [Credit.lean_cost,hy] at pay
  exact ⟨positive,reserve (A.outputNorm m) positive (h A) pay⟩

end YM.Integration.WilsonLimitConstruction.FundedNativePacketGeometry
end
