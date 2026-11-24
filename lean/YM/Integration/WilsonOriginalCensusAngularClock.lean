import YM.Integration.WilsonOriginalCollarWidthAtPost
import YM.Integration.WilsonOriginalCensusTariffDate

/-! Apply the teacher tariff to the issued physical budget and bond crop. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalCensusAngularClock
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





open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport WilsonEmittedFiledCatalogue
open WilsonEmittedWordJointFare WilsonOriginalCensusTariffDate

/-- One calendar cutoff works for every deposited physical face and every pair of fitted axes,
while the actual compact field and signed angular entries are read at their own sites. -/
theorem original (request:Request G)(simple:G.Simple)(φ:ℕ→ℕ)(R:Run G)
    (widths:WilsonOriginalCollarWidthReceipt.Open request simple φ R)
    (fixed:∀i,(R.family.path.levels.budget i).supportExponent=100)(κ:ℕ)
    {S:Type}[Fintype S](tube:LinkTube G)(pieces physical:ℕ)(p:Bool→ℕ)
    (span:S→ℕ)(lag:S→Bool→ℕ):
    ∀ᶠi:ℕ in atTop,∀ x,x≤R.family.path.levels.clock.J (i+1) →
      let D:=WilsonOlderFreshGraphSchool.roots (menu request) simple R.metals.p R.metals.K
      let σ:=Poetry.Agenda.seed D φ κ x
      let H:=R.family.path.levels.clock.hatBeta (i+1)
      ∀(m N per k:ℕ)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per)),
      Concourse R.alloy R.kit R.T π Γ m N per k Ψ → m ≤ i+1 → (i+1) ≤ N →
      0<σ ∧ Real.exp (σ⁻¹^2)≤H ∧
      ((Ψ (i+1)).p.supportExponent+2)*(((Ψ (i+1)).p.B:ℝ)⁻¹)≤σ/2 ∧
      (H/2≤(Ψ (i+1)).beta ∧ (Ψ (i+1)).beta≤2*H) ∧ (Real.sqrt (Ψ (i+1)).beta)⁻¹ ≤ 1/2 ∧
      (Ψ (i+1)).p.B=Nat.ceil ((Real.log H)^2) ∧ (Ψ (i+1)).p.supportExponent+2≤102 ∧
      ∀s,Begun tube pieces physical (3*span s) (span s) p (lag s) H:=by
  let χ:=fun i=>R.alloy.B.a.clock.hatBeta (i+1)
  have grows:Tendsto χ atTop atTop:=(RG01.Physical.hats simple R.alloy.B.a).comp (tendsto_add_atTop_nat 1)
  have issued (s:S):∀ᶠi:ℕ in atTop,Begun tube pieces physical (3*span s) (span s) p (lag s) (χ i):=
    grows.eventually (WilsonOriginalCensusTariffDate.original tube pieces physical (3*span s) (span s) p (lag s))
  filter_upwards [WilsonOriginalCollarWidthAtPost.original request simple φ R widths fixed κ,
    grows.eventually_ge_atTop 8,eventually_all.mpr issued] with i paid large entire
  intro x live D σ H m N per k π Γ Ψ course base top
  obtain ⟨positive,wage,placed,_⟩:=paid x live m N per k π Γ Ψ course base top
  have point:=(course.1.walk (i+1) base top).truep.point
  have therm: H/2≤(Ψ (i+1)).beta ∧ (Ψ (i+1)).beta≤2*H:=by
    rw [(course.1.walk (i+1) base top).beta]
    exact (R.makes.wilson.represents N per (i+1) top).band
  have big:8 ≤ H:=large
  have β:4≤(Ψ (i+1)).beta:=by linarith only [big,therm.1]
  have small:(Real.sqrt (Ψ (i+1)).beta)⁻¹ ≤ 1/2:=by
    rw [←one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have sq:=Real.sq_sqrt (show 0≤(Ψ (i+1)).beta by linarith only [β])
    nlinarith only [sq,β,Real.sqrt_nonneg (Ψ (i+1)).beta]
  refine ⟨positive,wage,placed,therm,small,?_,?_,entire⟩
  · rw [point];rfl
  · rw [point]
    change (R.family.path.levels.budget (i+1)).supportExponent+2 ≤ 102
    rw [fixed];norm_num

end YM.Integration.WilsonOriginalCensusAngularClock
end
