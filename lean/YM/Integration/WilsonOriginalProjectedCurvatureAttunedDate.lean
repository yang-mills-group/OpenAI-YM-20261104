import YM.Integration.WilsonOriginalProjectedCurvatureAffiliated
import YM.Integration.WilsonOriginalProjectedCurvatureFoundry
import YM.Integration.WilsonMovingMentorStartingHard
import YM.Integration.WilsonMovingMentorRaffleCourse
import YM.Integration.WilsonOriginalProjectedCurvatureArmada

/-! Spend the actual original interior hard reserve and the purchased invoice on
one representation of the physical Course, at the genuine regulator temperature. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureAttunedDate
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
      Affinity.Taut (paper D u).support (WilsonOriginalProjectedCurvatureTableau.actors D)
        (fun j=>(WilsonOriginalProjectedCurvatureTableau.nulls D j).restrictScalars ℝ) incoming.old ∧
      Affinity.Crown (paper D u).support (WilsonOriginalProjectedCurvatureTableau.actors D)
        (fun j=>(WilsonOriginalProjectedCurvatureTableau.nulls D j).restrictScalars ℝ) incoming.hard ∧
      (∀ radius grade,incoming.old.Paid w grade radius 0) ∧
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
  obtain ⟨actual,taut,crown,old,paid,field⟩:=WilsonOriginalProjectedCurvatureAffiliated.original Q D u μ orders N (aσ stage)
    extra (P) hard schedule invoice hd due glaw entry.view hG reached ready
  exact ⟨actual,taut,crown,old,QuadraticLocal.Hard.mono actual.hard paid net,field⟩

end YM.Integration.WilsonOriginalProjectedCurvatureAttunedDate
