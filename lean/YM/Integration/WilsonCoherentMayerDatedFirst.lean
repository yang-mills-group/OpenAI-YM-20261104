import YM.Integration.WilsonOriginalProjectedCurvatureEvaluation
import YM.Integration.WilsonMovingMentorDatedCourse

/-! Select the original quiet seed and the complete physical and finite first marked return together for two successive dates. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerDatedFirst
open Function Filter Finset Lattice Wilson RG Source Labels Marker Ac
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato LocalComparison
open ComparisonDensity.Address MergeProof MergeProof.Replicums Comparison.Density.RenderM FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureSalary
open QuadraticLocal QuadraticLocal.Earn Mentor MintClock AllOrder AllOrder.Transit AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset
open ConnectedActivityE6 Push.PriceCompiler FullQLocal FullQLocal.RenderedStep
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (hG:G.Simple) {B:MS.Local.Physical.Deck G}
  {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] (J:Request V) (Q:MS.Land.Prescription B)
  (u:V→MS.Rake.Label B) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ) {ψ:ℕ→ℕ}
  (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (seat:root.Tab R.rolls) (way:WayStation R.kit) (ticket:TicketP R.alloy R.kit root seat)
  (posted:Spill.Raffle.Warm G root R.alloy.delay ψ)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "h" => Fintype.card V
local notation "v" => h*t
local notation "rank" => ActualOriginalQLayout.rankCap R u

variable (books:Mentor.Offices.Books root R.rolls seat ψ) (forecast:Mentor.Forecast root R.rolls seat ψ books)
  (education:Mentor.Educated root R.rolls seat R.kit.shape R.kit.scout ψ books R.alloy.delay)
  (active:∀j,MintClock.Employment root ψ j (R.rolls.L j))
  (calendar:MintClock.Regency root R.rolls seat R.kit.target ψ books forecast R.alloy.delay)
  (hospital:MintClock.Hospital root R.rolls seat R.kit.target ψ books forecast R.alloy.delay)
  (pass:Pass root seat R.alloy R.kit)

open QuadraticLocal.Advent WilsonOriginalProjectedCurvatureTableau Laurent Stationary
open Tree
open RG RG01.Survive

include income way ticket posted active calendar hospital education pass
theorem original (warm:WilsonMovingMentorWarm.Conditions R.kit) (K grade q target quiet:ℕ)
    (ranked:rank≤grade) (quietOrder:quiet≤3*(grade+v+h)+2)
    (positive:∀j,0<w j) {ε:ℝ} (εpos:0<ε):
    ∃ C:ℝ,1≤C ∧ ∃ b:ℕ,∀ᶠ i:ℕ in atTop,
    let m:=i+1
    let N:=m+1
    ∀(op:Mentor.Opportunity (J₀ (m+1)) (J₀ m)) (epoch:Mentor.Epoch root R.rolls (J₀ (m+1)) (J₀ m) op),
    op.count=h → op.stage=grade+1 → epoch.vac=grade+v+h →
    let Ω:=Mentor.Cruise.Semester.expense root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
    let start : i ≤ m := Nat.le_succ i
    let before : m < N := Nat.lt_succ_self m
    4≤Ω ∧ Ω≤(β̂ (m+1))^(Beaming.grain (J₀ m)) ∧
    ∃ π Γ,PlanV.Path root R.alloy seat (Burn.horizon epoch.vac) N i π Γ ∧
    ∃ hk:Burn.horizon epoch.vac+2≤J₀ i,∃ lesson:Oak.Lesson (N:=N) R hk root seat π Γ start,
    ∀ p:ℕ,∃ H:(s:ℕ)→Rep G (R.family.side s p),
    Concourse R.alloy R.kit R.T π Γ i N p epoch.vac H ∧ Topline (H N) (R.family.path.levels.clock.forcedAllowance N) ∧
    (∀ age,i≤age → age≤N → (H age).beta=(R.family.path.rep N p age).beta ∧ (H age).eval=(R.family.path.rep N p age).eval ∧
      ∃ seed:Burn.Seed (H age) (M0 epoch.vac 0 (R.alloy.B.a.budget age) (π age) (R.family.path.rep N p age).beta),
        Burn.Candor (R.alloy.B.a.budget age) (H age).activities (Set.range seed.model) (Burn.silver (β̂ age))
          (ε*(Pert.Asymptotics.regulatorRun R.family N p age)^quiet)) ∧
    ∀ (o:V→Site (R.family.side (m+1) p)) (orders:V→ℕ), (∀z,orders z≤K) →
      let D:=ActualOriginalQPointSetup.pointDatum R J p (m+1) o
      let σ:=Poetry.Agenda.seed root ψ (Burn.horizon (grade+v+h)) (J₀ (m+1))
      let η:=(μ+R.family.S.scale N-R.family.S.scale (m+1))-R.family.S.scale N
      let X:=WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
      let a:=C*(β̂ (m+1))^(b+1)
      let weights:=fun j=>w j/(a*Ω)
      let g:=Coat.gStep (R.family.path.rep N p (m+1)).beta
      (∀ s:(Stock.census V).Mode,Poly.toll weights s*(a*Ω)^s.val.card=Poly.toll w s ∧
        (a*Ω)^s.val.card*g^(q+2*((b+1)*h)+1) ≤ ε*g^q) ∧
      ∃ _signed:∀i,0<weights i, ∃ voter:Mentor.Cruise.Voter X (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1))) grade op.count op.stage epoch.vac (J₀ m),
      ∃ incoming:Tint.Incoming (paper D u) (H (m+1)) (tastes D) Empty (Stock.census V),
        (∀ (x:tastes D) (U:Config G (R.family.side (m+1) p)),
          (Tint.Patrol.picture X incoming).density x U=
            ((ActualOriginalQInput.input Q D u η orders hG N before).leaf
              (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)).density U) ∧
        Scene.Armada X weights (fun _=>t) (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac)
            (J₀ (m+1))) Ω⁻¹ grade op.count v ∧
        ∃ ξ:Type, Countable ξ ∧ ∃ out,
          Oak.Buffered.SuccessStory R hk root seat π Γ H books start op lesson forecast
            (actors D) (fun i=>(nulls D i).restrictScalars ℝ) X incoming weights (fun _=>t)
            grade v voter ((β̂ (m+1))^(-(grade:ℝ))) Ω⁻¹ out (J:=ξ) ∧
          (∀ y,LocalComparison.actualPush R.family N p m
            (((ActualOriginalQInput.input Q D u η orders hG N before).leaf
              (testInclusion (ActualRunQlocalNativeTuple.orbit D) y)).density)=
            (Tint.Patrol.report (Oak.student (n:=p) R hk root seat π Γ books start op lesson forecast
                (actors D) X grade voter) out g).density y) ∧
          ∀ (x:tastes D) (F:Forest (R.family.path.levels.clock.op m p).ratio)
            (tag:(R.family.path.levels.clock.op m p).Choices) (A:Stationary.Link G (R.family.side m p)),
            WilsonOriginalMarkedEvaluation.Filed R hk root seat π Γ books start before op lesson forecast
              (actors D) X weights (fun _=>t) grade voter Ω⁻¹ x F tag A := by
  obtain ⟨C,cpos,b,purchases⟩:=WilsonOriginalProjectedCurvatureEvaluation.original R hG J Q u μ extra w root seat
    way ticket posted income books forecast education active calendar hospital pass K grade q target ranked positive εpos
  have quietCourse:=WilsonMovingMentorDatedCourse.original R hG warm pass quiet (grade+v+h) quietOrder εpos
  refine ⟨C,cpos,b,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually purchases, quietCourse,
    R.family.path.levels.fits.deep.eventually_ge_atTop (Burn.horizon (grade+v+h)+2)] with i paid dated deep
  intro m N op epoch count stage cap Ω start before
  obtain ⟨large,roof,issued⟩:=paid op epoch count stage cap
  obtain ⟨π,Γ,path,byPeriod⟩:=dated N (le_trans start before.le)
  rw [←cap] at path byPeriod deep
  let lesson:Oak.Lesson (N:=N) R deep root seat π Γ start:=(Oak.tale R deep root seat π Γ start before path).some
  refine ⟨large,roof,π,Γ,path,deep,lesson,?_⟩
  intro p
  obtain ⟨H,course,top,stocks⟩:=byPeriod p
  refine ⟨H,course,top,stocks,?_⟩
  intro o orders capped
  exact issued N p o orders capped before π Γ H i start course deep lesson top

end YM.Integration.WilsonCoherentMayerDatedFirst
