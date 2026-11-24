import YM.Integration.WilsonOriginalCollarWidthReceipt

/-! Apply the teacher tariff to the issued physical budget and bond crop. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalCollarWidthAtPost
open Filter Function Finset Lattice Laurent Wilson RG RG.Supply Precision Input Org Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor QuadraticLocal.Advent.Sycamore QuadraticLocal.Rebirth
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonFundedWindowCompany WilsonFundedWindowMenu WilsonWindowJointPurchase WilsonWindowBookPurchase
open WilsonReportingAbsoluteInletSchool WilsonWindowUniversalSchool
open FormalBulk08 FormalBulk08.Flat Push.PriceCompiler
open OPE.Owl WilsonCoeffUV WilsonCoeffUV.Bank
open LocalComparison
open WilsonOriginalCollarElection WilsonOriginalCollarTeacher QuadraticLocal.Advent.Oak QuadraticLocal.Affinity
open WilsonLimitConstruction.FundedDictionaryPatchPrices
open scoped Classical BigOperators Topology
universe u
variable {G : Gauge} {φ : ℕ → ℕ}





theorem bonds {σ H : ℝ} (hs : 0 < σ) (bill : Real.exp (σ⁻¹^2) ≤ H) :
    Real.sqrt (Real.log H)^3 ≤ σ * (Nat.ceil ((Real.log H)^2):ℝ) := by
  have slope := (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le bill)).2 bill
  let x := Real.sqrt (Real.log H)
  have xn : 0 ≤ x := Real.sqrt_nonneg _
  have xs : x^2=Real.log H := Real.sq_sqrt ((sq_nonneg _).trans slope)
  have xl : σ⁻¹ ≤ x := by
    by_contra! down
    nlinarith [mul_pos (sub_pos.mpr down) (add_pos_of_pos_of_nonneg (inv_pos.mpr hs) xn)]
  have gain := mul_le_mul_of_nonneg_left xl hs.le
  rw [mul_inv_cancel₀ hs.ne'] at gain
  calc
    x^3 = x^3*1 := by ring
    _ ≤ x^3*(σ*x) := mul_le_mul_of_nonneg_left gain (pow_nonneg xn _)
    _ = σ * (Real.log H)^2 := by rw [← xs]; ring
    _ ≤ σ * (Nat.ceil ((Real.log H)^2):ℝ) := mul_le_mul_of_nonneg_left (Nat.le_ceil _) hs.le

/-- The numerical charge holds on the particular returned parent budget for
each admitted tagged course. The short-bond power grows at that date. -/
theorem original (request : Request G) (simple : G.Simple) (φ : ℕ → ℕ) (R : Run G)
    (widths : WilsonOriginalCollarWidthReceipt.Open request simple φ R)
    (fixed : ∀ i,(R.family.path.levels.budget i).supportExponent=100) (κ : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ x, x ≤ R.family.path.levels.clock.J (i+1) →
      let D := WilsonOlderFreshGraphSchool.roots (menu request) simple R.metals.p R.metals.K
      let σ := Poetry.Agenda.seed D φ κ x
      let H := R.family.path.levels.clock.hatBeta (i+1)
      ∀ (m N per k : ℕ) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
        (Ψ : ∀ j, RG.Rep G (R.family.side j per)),
        Concourse R.alloy R.kit R.T π Γ m N per k Ψ → m ≤ i+1 → i+1 ≤ N →
        0<σ ∧ Real.exp (σ⁻¹^2) ≤ H ∧
        ((Ψ (i+1)).p.supportExponent+2)*(((Ψ (i+1)).p.B:ℝ)⁻¹) ≤ σ/2 ∧
        Real.sqrt (Real.log H)^3 ≤ σ*((Ψ (i+1)).p.B:ℝ) := by
  filter_upwards [widths κ] with i paid
  intro x live
  dsimp only
  intro m N per k π Γ Ψ course lo hi
  obtain ⟨positive,invoice,placed⟩ := paid x live
  have point : (Ψ (i+1)).p = R.family.path.levels.budget (i+1) := (course.1.walk (i+1) lo hi).truep.point
  have size : (Ψ (i+1)).p.B=Nat.ceil ((Real.log (R.family.path.levels.clock.hatBeta (i+1)))^2) := by rw [point];rfl
  refine ⟨positive,invoice,?_,?_⟩
  · rw [size,point,fixed]
    convert placed using 1
    norm_num [div_eq_mul_inv]
  · rw [size]
    exact bonds positive invoice

end YM.Integration.WilsonOriginalCollarWidthAtPost
end
