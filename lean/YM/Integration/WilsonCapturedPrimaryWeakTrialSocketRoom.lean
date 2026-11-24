import YM.Integration.WilsonOriginalCensusAngularClock
import YM.Integration.WilsonEmittedOriginalRoom
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWeakTrialSocketRoom
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


private theorem inner (B:BudgetPoint)(n:Side)(tube:LinkTube G)(w:ℝ)
    (wide:Room B n tube (B.B+1) w):Room B n tube B.B w:=by
  have grow:axialCost B B.B ≤ axialCost B (B.B+1):=by
    unfold axialCost
    gcongr
    · exact B.threshold_pos.le
    · exact Nat.le_succ _
  exact ⟨lt_of_le_of_lt (by omega) wide.side,grow.trans_lt wide.core,
    (mul_le_mul_of_nonneg_left grow tube.scale.le).trans wide.logs,wide.budget,wide.small⟩

/-- A single opening buys the geometric room and the two thermal sides on every later physical mesh. -/
theorem original (R:Run G)(simple:G.Simple)(tube:LinkTube G)(physical target:ℕ)(issued delay:Bool→ℕ):
    ∀ᶠ j:ℕ in atTop,∀(N per:ℕ),j≤N→∀W:RG.Rep G (R.family.side j per),
      W.p=R.family.path.levels.budget j → W.beta=R.family.path.β N per j →
      let H:=R.family.path.levels.clock.hatBeta j
      let g:=(Real.sqrt W.beta)⁻¹
      let w:=WilsonEmittedCubeRoom.width R.family.path.levels tube j
      Room W.p (R.family.side j per) tube W.p.B w ∧ 0≤w ∧ w≤2*g^(1/2:ℝ) ∧
      H/2≤W.beta ∧ W.beta≤2*H ∧ g≤1/2 ∧ W.p.B=Nat.ceil ((Real.log H)^2) ∧
      WilsonOriginalCensusTariffDate.Begun tube 3 physical (3*target) target issued delay H:=by
  let A:=R.family.path.levels
  have rise:=RG01.Physical.hats simple A
  filter_upwards [WilsonEmittedOriginalRoom.original A tube simple,
    WilsonEmittedOriginalRoom.width_paid A tube simple (by norm_num:0<(1/2:ℝ)),
    rise.eventually_ge_atTop 8,rise.eventually (WilsonOriginalCensusTariffDate.original tube 3 physical (3*target) target issued delay)] with j room paid large begin
  intro N per live W params heat H g w
  have thermal:H/2≤W.beta ∧ W.beta≤2*H:=by rw [heat];exact (R.makes.wilson.represents N per j live).band
  have big:8≤H:=large
  have positive:4≤W.beta:=by linarith only [big,thermal.1]
  have small:g≤1/2:=by
    change (Real.sqrt W.beta)⁻¹≤1/2
    rw [←one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    have sq:=Real.sq_sqrt (show 0≤W.beta by linarith only [positive])
    nlinarith only [sq,positive,Real.sqrt_nonneg W.beta]
  have interior:Room W.p (R.family.side j per) tube W.p.B w:=by rw [params];exact inner _ _ _ _ (room per)
  refine ⟨interior,W.p.threshold_pos.le.trans interior.budget,?_,thermal.1,thermal.2,small,?_,begin⟩
  · have exponent:1-(1/2:ℝ)=1/2:=by norm_num
    simpa only [exponent] using paid W.beta thermal.1 thermal.2
  · rw [params];rfl

end YM.Integration.WilsonCapturedPrimaryWeakTrialSocketRoom
