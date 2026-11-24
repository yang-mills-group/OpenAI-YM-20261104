import YM.Integration.WilsonOriginalBlissQPost

/-! On the original marked school, keep its one common path before the periodic folds and its actual measured vacuum at every age. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissQChronology
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra
open QuadraticLocal.Rebirth ConnectedActivityE6 FullQLocal FullQLocal.RenderedStep
open Multi Exterior WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open Source Labels LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonMixedPassportVote
open Pert.Asymptotics Extra.Histories WilsonOriginalReceivedChain
open scoped Classical BigOperators
open VowsR QuadraticLocal.Affinity Sycamore
variable {G:Gauge} (R:Run G) (simple:G.Simple)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  {φ:ℕ→ℕ} (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (ahead:Mentor.Forecast D R.rolls Q φ books) {ZΘ:ℝ} {profile:PhysicalNext.ThroughLaunch.Orders}
  (house:Treehouse.VariableHouse R D Q scroll books ZΘ ahead profile)

private def school (k:ℕ)(pos:0 < k):Syl.School k where
  order:=2
  pieces:=0
  horizon:=0
  sense:=Nat.zero_le _
  price:=by unfold Burn.horizon; omega
  tall:=by unfold Burn.horizon; omega

def Closed (k:ℕ)(first:ℕ):Prop:=
  ∀N,first ≤ N → ∃ (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J first),
    (∀ m (floor:first ≤ m),m<N → Nonempty (Oak.Lesson (N:=N) R hk D Q π Γ floor)) ∧
    PlanV.Path D R.alloy Q (Burn.horizon k) N first π Γ ∧ ∀ per,
    ∃ H:(i:ℕ)→RG.Rep G (R.family.side i per),
      Concourse R.alloy R.kit R.T π Γ first N per k H ∧
      Topline (H N) (R.family.path.levels.clock.forcedAllowance N) ∧
      ∀ i,first ≤ i → i ≤ N →
        (H i).beta=(R.family.path.rep N per i).beta ∧ (H i).eval=(R.family.path.rep N per i).eval

include house in
theorem original (k:ℕ)(pos:0 < k):∀ᶠ first in Filter.atTop,Closed R D Q k first:=by
  let S:=school k pos
  have big:2 ≤ S.order:=le_rfl
  have visit:=house.across k S 0 0 0 0 0 0 0 0 (1/16) 0 (1/8) 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) big (by norm_num)
  obtain ⟨onset,bought⟩:=Filter.eventually_atTop.mp visit
  filter_upwards [Filter.eventually_ge_atTop onset] with first late
  have zero:PaceR.Close R 0 0 first first:=by simp [PaceR.Close]
  obtain ⟨visit,_⟩:=bought first late first le_rfl zero
  intro N top
  obtain ⟨π,Γ,hk,lessons,path,periods⟩:=visit.era le_rfl N top
  refine ⟨π,Γ,hk,fun m hm live=>⟨lessons m hm live⟩,path,?_⟩
  intro per
  obtain ⟨H,bank⟩:=periods per
  refine ⟨H,bank.conc,bank.topline,?_⟩
  intro i lo hi
  have posted:=bank.conc.1.walk i lo hi
  exact ⟨posted.beta,posted.view⟩

end YM.Integration.WilsonOriginalBlissQChronology
end
