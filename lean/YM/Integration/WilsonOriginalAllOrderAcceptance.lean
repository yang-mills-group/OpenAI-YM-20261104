import YM.Integration.WilsonOriginalAllOrderCourse
import YM.Integration.WilsonOriginalCollarWidthAtPost

/-! Read the original run at an arbitrary finite order after the public
hierarchy is chosen, on its compiling gear and on its funded physical posts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalAllOrderAcceptance
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
open WilsonOriginalAllOrderCalendar
open WilsonOriginalAllOrderCourse
universe u
variable {G : Gauge} {a : Axis} {simple : G.Simple} {ε : ℝ} {s : WilsonOriginalAllOrderCourse.Schedule G}
variable {R : Run G} {T : Campaign R} {W : Campaign.Pillars R T}

/-- Every finite key enters the increasing calendar and pays its two original
widths at all sufficiently fine dates, with the old kinetic clock unchanged. -/
theorem enrolled (p : WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W) (key : Key) (H : ℕ) :
    ∀ᶠ i : ℕ in atTop,
      let j := R.alloy.B.a.clock.J i
      let K := R.metals.p.kernel
      let L := R.alloy.B.a.clock.factor j
      let BH := R.alloy.B.a.clock.hatBeta i
      (s.neutral key).entrance K j (R.metals.p.profile j) ≤ L.val ∧
      (s.extraStrip key).threshold K j ≤ (R.rolls.L j).val ∧
      ∃ μ τ : ℝ, 0 < μ ∧ Real.exp (μ⁻¹^2) ≤ BH ∧ 0 < τ ∧ Real.exp (τ⁻¹^2) ≤ BH ∧
        μ ≤ WilsonThermometerUnitFilingWeakStrip.trial (s.neutral key) K j H ∧
        τ ≤ (s.extraStrip key).cap K j H ∧
        (s.extraStrip key).bill K j H ≤ budgetR R i := by
  filter_upwards [R.alloy.B.a.fits.deep.eventually_ge_atTop (Encodable.encode key),
    R.alloy.B.a.fits.deep.eventually_ge_atTop H] with i active enough
  intro j K L BH
  have neutral := WilsonOriginalAllOrderFiledRealm.entrance (rows s) R p.neutral i H enough
  obtain ⟨muPos,muCost,grant,_⟩ := neutral
  obtain ⟨gate,short⟩ := grant (Encodable.encode key) active
  obtain ⟨τ,τpos,_,τcost,income⟩ := p.stripsPaid i H enough
  obtain ⟨floor,strip,fee⟩ := income (Encodable.encode key) active
  simp only [rows,strips,indexed] at gate floor short strip fee
  exact ⟨gate,floor,_,τ,muPos,muCost,τpos,τcost,short,strip,fee⟩

/-- The retained width is an invoice on the actual tagged physical teacher,
with all original periods and cutoffs quantified after its opening. -/
theorem at_post (p : WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W) (κ : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ x, x ≤ R.family.path.levels.clock.J (i+1) →
      let D := WilsonOlderFreshGraphSchool.roots (menu (teacher s)) simple R.metals.p R.metals.K
      let σ := Poetry.Agenda.seed D MintClock.splits κ x
      let H := R.family.path.levels.clock.hatBeta (i+1)
      ∀ (m N per k : ℕ) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
        (Ψ : ∀ j, RG.Rep G (R.family.side j per)),
        Concourse R.alloy R.kit R.T π Γ m N per k Ψ → m ≤ i+1 → i+1 ≤ N →
        0<σ ∧ Real.exp (σ⁻¹^2) ≤ H ∧
        ((Ψ (i+1)).p.supportExponent+2)*(((Ψ (i+1)).p.B:ℝ)⁻¹) ≤ σ/2 ∧
        Real.sqrt (Real.log H)^3 ≤ σ*((Ψ (i+1)).p.B:ℝ) :=
  WilsonOriginalCollarWidthAtPost.original (teacher s) simple MintClock.splits R p.first p.support κ

/-- Fix the public family on the full original ordered regulator. This single
family is available for all requested finite panels. -/
theorem published (a : Axis) (simple : G.Simple) {ε : ℝ} (positive : 0 < ε) (s : WilsonOriginalAllOrderCourse.Schedule G) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W ∧
      WilsonOriginalAllOrderPublicFields.Master.{u} R simple (fun _ => True) Extraction.Order.full := by
  obtain ⟨R,T,W,paid⟩ := WilsonOriginalAllOrderCourse.original.{u} a simple positive s
  exact ⟨R,T,W,paid,paid.physical (fun _ => True) (fun _ _ _ => trivial) Extraction.Order.full⟩

end YM.Integration.WilsonOriginalAllOrderAcceptance
end
