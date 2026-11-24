import YM.Integration.WilsonReceivedCloseElectedProgram

/-! A pointed source is assigned its graded physical school before the cutoff and period.
The original Wilson ledger and its actual reporting appointments remain on the same course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointHouseSeats
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


def order (Q q : ℕ) := Q+2*((q+2+2)+4+1)+8
def vacuum (d Q q : ℕ) := order Q q+d+q+4
def school (d Q q : ℕ) : Syl.School (vacuum d Q q) :=
  ⟨order Q q,1,d,by unfold vacuum Burn.horizon; omega,
    by unfold vacuum Burn.horizon; omega,by unfold vacuum Burn.horizon; omega⟩

theorem grade (d Q q : ℕ) :
    let S:=school d Q q
    2*((q+2+2)+4+1)+8 ≤ S.order ∧ Q ≤ S.order ∧ (q+2+2)+4+4 ≤ 3*vacuum d Q q+2 ∧
      0<S.pieces ∧ d ≤ S.horizon ∧ 2 ≤ S.order ∧ 1 ≤ Burn.horizon (vacuum d Q q) := by
  dsimp [school,vacuum,order,Burn.horizon]
  omega

variable {k : ℕ}
def Seats (S : Syl.School k) (first : ℕ) : Prop :=
  ∀N,first ≤ N → ∃ (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J first)
    (lessons:∀i, ∀ (lo : first ≤ i), i < N → Oak.Lesson (N:=N) R hk D Q π Γ lo),
    PlanV.Path D R.alloy Q (Burn.horizon k) N first π Γ ∧
    ∀per, ∃ Ψ:(i:ℕ)→RG.Rep G (R.family.side i per),
      Concourse R.alloy R.kit R.T π Γ first N per k Ψ ∧
      Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N) ∧
      ∀i (lo:first ≤ i) (live:i < N),
        Nonempty (Oak.Calendar R hk D Q π Γ Ψ lo (N:=N) (lessons i lo live)) ∧
        ∃ op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i),
          op.count=S.pieces ∧ op.stage=S.order+1

include house in
theorem original (S : Syl.School k) (deep : 2 ≤ S.order) :
    ∀ᶠ first in atTop, Seats R D Q S first := by
  have visit:=house.across k S 0 0 0 0 0 0 0 0 (1/16) 0 (1/8) 1 0 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) deep (by norm_num)
  obtain ⟨start,bought⟩:=Filter.eventually_atTop.mp visit
  filter_upwards [Filter.eventually_ge_atTop start] with first late
  have close:PaceR.Close R 0 0 first first:=by simp [PaceR.Close]
  obtain ⟨stay,_⟩:=bought first late first le_rfl close
  intro N top
  obtain ⟨π,Γ,hk,lessons,path,periods⟩:=stay.era le_rfl N top
  refine ⟨π,Γ,hk,lessons,path,?_⟩
  intro per
  obtain ⟨Ψ,bank⟩:=periods per
  refine ⟨Ψ,bank.conc,bank.topline,?_⟩
  intro i lo live
  exact ⟨Oak.agrees R hk D Q π Γ Ψ bank.conc lo live (lessons i lo live),
    S.room (Push.PriceCompiler.step_paid R.alloy.B.a i)
      (hk.trans (R.alloy.B.a.fits.mono lo)), rfl, rfl⟩

include house in
theorem pointed (d order q : ℕ) :
    ∀ᶠ first in atTop, Seats R D Q (school d order q) first :=
  original R D Q scroll books ahead house (school d order q) (grade d order q).2.2.2.2.2.1

end YM.Integration.WilsonMeasuredPointHouseSeats
end
