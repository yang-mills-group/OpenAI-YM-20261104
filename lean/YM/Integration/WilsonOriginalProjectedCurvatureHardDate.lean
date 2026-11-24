import YM.Integration.WilsonOriginalProjectedCurvatureFoundry
import YM.Integration.WilsonMovingMentorStartingHard
import YM.Integration.WilsonMovingMentorRaffleCourse
import YM.Integration.WilsonOriginalProjectedCurvatureArmada

/-! Spend the actual original interior hard reserve and the purchased invoice on
one representation of the physical Course, at the genuine regulator temperature. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureHardDate
open Function Finset Lattice Wilson RG Source Labels Marker Ac
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato LocalComparison
open ComparisonDensity.Address MergeProof MergeProof.Replicums Comparison.Density.RenderM FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureSalary
open QuadraticLocal QuadraticLocal.Earn Mentor MintClock AllOrder AllOrder.Transit AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit.WheelP
open ConnectedActivityE6 Push.PriceCompiler
open FullQLocal FullQLocal.RenderedStep
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {B:MS.Local.Physical.Deck G}
  {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] (Q:MS.Land.Prescription B)
  {i n p N seed first:ℕ} {ni:n ≤ i} (D:ActualRunQlocalNativeTuple.Datum R p i n ni V)
  (u:V→MS.Rake.Label B) (μ:ℝ) (orders:V→ℕ) (extra:V→ℕ)
  (hG:G.Simple) (ready:∀s:Slot u,R.family.ref s.2.size ≤ i)
  {ψ:ℕ→ℕ} (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (seat:root.Tab R.rolls) (way:WayStation R.kit) (ticket:TicketP R.alloy R.kit root seat)
  (posted:Spill.Raffle.Warm G root R.alloy.delay ψ)
  {π:ℕ→Layout G} {Γ:ℕ→Pace.Coin} {H:(s:ℕ)→Rep G (R.family.side s p)}
  (story:Concourse R.alloy R.kit R.T π Γ first N p seed H) (start:first ≤ i) (reached:i ≤ N)
  (top:Topline (H N) (R.family.path.levels.clock.forcedAllowance N))
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "step" => R.alloy.B.a.clock.J i
local notation "aσ" K:max => Poetry.Agenda.seed root ψ K step
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p i
local notation "X" K:max => WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N (aσ K) extra
local notation "P" => H i

include ready way ticket posted
include story start top in
theorem measured {w:V→ℝ} {t:V→ℕ} {stage rank h vol target:ℕ}
    (schedule:Scene.Armada (X stage) w t (aσ stage) 1 rank h vol)
    (s₀:stage ≤ step) (s₁:rank ≤ step) (s₂:vol ≤ step) (s₃:h ≤ step)
    (attained:target+Spill.Raffle.pad (rank+vol+1)*h ≤ step) :
    ∃ incoming:Tint.Incoming (paper D u) (P) (tastes D) Empty (Stock.census V),
      incoming.hard.Paid w (P).p.B (P).p.supportExponent
        ((β̂ i)^(-(target:ℝ))*forcedDivisor R.family i) ∧
      ∀ (x:tastes D) (U:Config G (R.family.side i p)),
        let input := (ActualOriginalQInput.input Q D u μ orders hG N reached).leaf
          (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)
        (Tint.Patrol.picture (X stage) incoming).density x U=input.density U := by
  let e:=Spill.Raffle.pad (rank+vol+1)
  have entry:=story.1.walk i start reached
  have glaw:g₀=Coat.gStep (P).beta:=by rw [entry.beta]; rfl
  obtain ⟨f,hard,net⟩:=WilsonMovingMentorStartingHard.throughout R way root seat π Γ H story ticket
    start target e h reached attained top
  obtain ⟨invoice,raw⟩:=WilsonMovingMentorRaffleCourse.measured R posted story start s₀ s₁ s₂ s₃ reached
  have temp:Spes.Market.tuning (R.metals.p.profile step) (P).p (β̂ i):=by
    rw [entry.truep.point, ←params_eq R.alloy.B.valid i]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  let d:ℝ:=(β̂ i)^e
  have hd:1 ≤ d:=one_le_pow₀ (R.alloy.B.a.fits.delayed i).le
  have fixed:=Spill.Raffle.regular G (R.metals.p.profile step) (aσ stage) rank vol h (P).p (β̂ i)
    temp.2.2 temp.2.1
  rw [←glaw] at invoice
  have due:(Spill.allOver (P).p)^(rank+vol+1)*
      (Invoice.price (P).p (Page.temperature G 1 (β̂ i)) (rank+vol+1) h ((P).p.supportExponent+1) ((aσ stage)/4) G*1)
      ≤ Willow.haloSlack (P).p.B*d:=by
    rw [mul_one,fixed]; exact raw.trans_eq (mul_comm ..)
  obtain ⟨actual,paid,field⟩:=WilsonOriginalProjectedCurvatureFoundry.original Q D u μ orders N (aσ stage)
    extra (P) hard schedule invoice hd due glaw entry.view hG reached ready
  exact ⟨actual,QuadraticLocal.Hard.mono actual.hard paid net,field⟩


/-- The filing and marker normalization precede all actual torus sizes. -/
theorem original (J:Request V) (w:V→ℝ) (positive:∀j,0<w j) (K stage target:ℕ)
    (s₀:stage ≤ step) (s₁:ActualOriginalQLayout.rankCap R u ≤ step)
    (s₂:Fintype.card V*WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u ≤ step)
    (s₃:Fintype.card V ≤ step) (attained:target+
      Spill.Raffle.pad (ActualOriginalQLayout.rankCap R u + Fintype.card V*WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u+1)*
      Fintype.card V ≤ step) :
    ∃ C:ℝ,0<C ∧ ∃ b:ℕ, ∀ (Ω:ℝ),1 ≤ Ω → ∀ (N p:ℕ) (o:V→Site (R.family.side i p)) (order:V→ℕ),
      (∀j,order j ≤ K) → ∀ (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (H:(s:ℕ)→Rep G (R.family.side s p))
      {first seed:ℕ} (_story:Concourse R.alloy R.kit R.T π Γ first N p seed H),
      first ≤ i → ∀ reached:i ≤ N, Topline (H N) (R.family.path.levels.clock.forcedAllowance N) → 0<Pert.Asymptotics.regulatorRun R.family N p i →
      Pert.Asymptotics.regulatorRun R.family N p i ≤ 1 →
      let D₀:=ActualOriginalQPointSetup.pointDatum R J p i o
      let asked:=WilsonOriginalProjectedCurvatureClock.charge R J u (aσ stage) (aσ stage) extra w
      let a:=max 1 ((C*(1+‖R.family.S.scale N‖)^b)*asked)
      let X₀:=WilsonOriginalProjectedCurvatureLamps.cohort Q D₀ u (μ-R.family.S.scale N) order N (aσ stage) extra
      (∀ mode:(Stock.census V).Mode,Poly.toll (fun j=>w j/(a*Ω)) mode*(a*Ω)^mode.val.card=Poly.toll w mode) ∧
      ∃ incoming:Tint.Incoming (paper D₀ u) (H i) (tastes D₀) Empty (Stock.census V),
        incoming.hard.Paid (fun j=>w j/(a*Ω)) (H i).p.B (H i).p.supportExponent
          ((β̂ i)^(-(target:ℝ))*forcedDivisor R.family i) ∧
        ∀ (x:tastes D₀) (U:Config G (R.family.side i p)),
          let input:=(ActualOriginalQInput.input Q D₀ u (μ-R.family.S.scale N) order hG N reached).leaf
            (testInclusion (ActualRunQlocalNativeTuple.orbit D₀) x)
          (Tint.Patrol.picture X₀ incoming).density x U=input.density U := by
  obtain ⟨C,hC,b,filing⟩:=WilsonOriginalProjectedCurvatureArmada.original (run:=R) (J:=J) (Q:=Q) (u:=u) (μ:=μ) (σ:=aσ stage) (extra:=extra) (w:=w) K positive
  refine ⟨C,hC,b,?_⟩
  intro Ω hΩ N p o order bound π Γ H first seed history start reached top lo hi D₀ asked a X₀
  obtain ⟨funded,restore⟩:=filing N p i o order bound reached lo hi Ω (zero_lt_one.trans_le hΩ)
  have installed:Scene.Armada X₀ (fun j=>w j/(a*Ω)) (fun _=>WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u)
      (aσ stage) 1 (ActualOriginalQLayout.rankCap R u) (Fintype.card V)
      (Fintype.card V*WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u):=
    { toMinistry:=funded.toMinistry,positive:=funded.positive,purchases:=funded.purchases,honor:=funded.honor
      suggests:=fun x=>Push.AbsoluteSums.budget_loosen (funded.suggests x) (inv_le_one_of_one_le₀ hΩ) }
  exact ⟨restore,measured R Q D₀ u (μ-R.family.S.scale N) order extra hG ready root seat way ticket posted
    history start reached top installed s₀ s₁ s₂ s₃ attained⟩

end YM.Integration.WilsonOriginalProjectedCurvatureHardDate
