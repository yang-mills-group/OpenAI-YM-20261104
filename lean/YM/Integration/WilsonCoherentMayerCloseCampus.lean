import YM.Integration.WilsonCoherentMayerDatedFirst
import YM.QuadraticLocal.Class.Venture
import YM.Integration.WilsonCoherentMayerMutationIntake
import YM.Integration.WilsonCoherentMayerSecondFiling

/-! The actual elected opportunity, epoch, lesson and first returned marked enrolment for every two consecutive dates. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerCloseCampus
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
open RG RG01.Survive QuadraticLocal.Rebirth

def curriculum (grade shelf pieces:ℕ) : QuadraticLocal.Syl.School (grade+shelf+pieces) where
  order:=grade
  pieces:=pieces
  horizon:=shelf
  sense:=by unfold Burn.horizon; omega
  price:=by unfold Burn.horizon; omega
  tall:=by unfold Burn.horizon; omega

include income way ticket posted active calendar hospital education pass
theorem original (month:Scholar.Month R.rolls root seat R.alloy.delay) (warm:WilsonMovingMentorWarm.Conditions R.kit) (K grade q target quiet:ℕ)
    (ranked:rank≤grade) (quietOrder:quiet≤3*(grade+v+h)+2)
    (positive:∀j,0<w j) {margin ε:ℝ} (gain:0 < margin) (unit:margin≤1) (εpos:0<ε):
    ∃ C:ℝ,1≤C ∧ ∃ b:ℕ,∀ᶠ first:ℕ in atTop,∀N:ℕ,first≤N →
    ∃π Γ,∃route:PlanV.Path root R.alloy seat (Burn.horizon (grade+v+h)) N first π Γ,
    ∃hk:Burn.horizon (grade+v+h)+2 ≤ J₀ first,
    ∀p:ℕ,∃ H:(s:ℕ)→Rep G (R.family.side s p),
      Concourse R.alloy R.kit R.T π Γ first N p (grade+v+h) H ∧
      Topline (H N) (R.family.path.levels.clock.forcedAllowance N) ∧
      (∀age,first≤age → age≤N → (H age).beta=(R.family.path.rep N p age).beta ∧
        (H age).eval=(R.family.path.rep N p age).eval ∧
        ∃seed:Burn.Seed (H age) (M0 (grade+v+h) 0 (R.alloy.B.a.budget age) (π age) (R.family.path.rep N p age).beta),
          Burn.Candor (R.alloy.B.a.budget age) (H age).activities (Set.range seed.model) (Burn.silver (β̂ age))
            (ε*(Pert.Asymptotics.regulatorRun R.family N p age)^quiet)) ∧
    ∀ (i : ℕ) (late : first ≤ i) (before : i + 1 < N),
    let m:=i+1
    let start : first ≤ m := late.trans (Nat.le_succ i)
    let op:=(curriculum grade v h).room (Push.PriceCompiler.step_paid R.alloy.B.a m) (hk.trans (R.alloy.B.a.fits.mono start))
    let lesson:Oak.Lesson (N:=N) R hk root seat π Γ start:=(Oak.tale R hk root seat π Γ start before route).some
    let epoch:=Oak.era R hk root seat π Γ start op lesson
    let Ω:=Mentor.Cruise.Semester.expense root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
    4≤Ω ∧ Ω≤(β̂ (m+1))^(Beaming.grain (J₀ m)) ∧
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
          (∀ (x:tastes D) (F:Forest (R.family.path.levels.clock.op m p).ratio)
            (tag:(R.family.path.levels.clock.op m p).Choices) (A:Stationary.Link G (R.family.side m p)),
            WilsonOriginalMarkedEvaluation.Filed R hk root seat π Γ books start before op lesson forecast
              (actors D) X weights (fun _=>t) grade voter Ω⁻¹ x F tag A) ∧
          let M₁:=Oak.student (n:=p) R hk root seat π Γ books start op lesson forecast (actors D) X grade voter
          let ζ:=Oak.grade0 R hk root seat π Γ start lesson
          let depth:=Burn.horizon epoch.vac+2
          let g₁:=Coat.gStep (H (m+1)).beta
          let g₀:=Coat.gStep (H m).beta
          let stamped:=Mutation.stamp M₁ (Γ m) ζ depth grade
          let corrected:=Mutation.grow M₁ (Γ m) ζ depth grade g₁ g₀ (H m) out
          let debt:=Mutation.mend M₁ (H m).p (Γ m) ζ depth grade g₁ g₀
          corrected.hard=out.hard ∧ corrected.old=debt.join out.old ∧
          debt.Paid weights (H m).p.B ((H m).p.supportExponent+1+1)
            (ε*g^((grade:ℝ)+1-margin)*Ω⁻¹) ∧
          ∀(x:tastes D) (Q₁:MS.Land.Prescription B) (u₁:V→MS.Rake.Label B) (o₁:V→Site (R.family.side m p))
              (orders₁:V→ℕ) (μ₁:ℝ),
            let D₁:=ActualOriginalQPointSetup.pointDatum R J p m o₁
            WilsonCoherentMayerSecondFiling.Joint (N:=N) Q₁ D₁ u₁ μ₁ orders₁
              (((ActualOriginalQInput.input Q D u η orders hG N before).leaf
                (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)).density)
              ((Tint.Patrol.picture stamped corrected).density x) := by
  obtain ⟨C,cpos,b,earn⟩:=WilsonOriginalProjectedCurvatureEvaluation.original R hG J Q u μ extra w root seat way ticket
    posted income books forecast education active calendar hospital pass K grade q target ranked positive εpos
  have actual:=WilsonMovingMentorDatedCourse.original R hG warm pass quiet (grade+v+h) quietOrder εpos
  obtain ⟨minDate,calendar₁⟩:=eventually_atTop.mp earn
  obtain ⟨minShelf,calendar₂⟩:=eventually_atTop.mp (R.alloy.B.a.fits.deep.eventually_ge_atTop v)
  refine ⟨C,cpos,b,?_⟩
  filter_upwards [actual,eventually_ge_atTop minDate,eventually_ge_atTop minShelf,
      eventually_ge_atTop (WilsonCoherentMayerMutationIntake.firstDate R hG grade gain unit εpos),
      R.alloy.B.a.fits.deep.eventually_ge_atTop (Burn.horizon (grade+v+h)+2)] with first selected echelon shelf openDate high
  intro N activeN
  obtain ⟨π,Γ,path,periods⟩:=selected N activeN
  refine ⟨π,Γ,path,high,?_⟩
  intro p
  obtain ⟨H,course,top,stock⟩:=periods p
  refine ⟨H,course,top,stock,?_⟩
  intro i late before m start op lesson epoch Ω
  have count:op.count=h:=rfl
  have stage:op.stage=grade+1:=rfl
  have cap:epoch.vac=grade+v+h:=rfl
  have narrow:=calendar₂ m (shelf.trans start)
  obtain ⟨large,roof,issued⟩:=calendar₁ m (echelon.trans start) op epoch count stage cap
  refine ⟨large,roof,?_⟩
  intro o orders capped D σ η X a weights g
  obtain ⟨bill,wp,voter,incoming,enter,army,ξ,nξ,out,story,law,filed⟩:=issued N p o orders capped before π Γ H first start course high lesson top
  refine ⟨bill,wp,voter,incoming,enter,army,ξ,nξ,out,story,law,filed,?_⟩
  intro M₁ ζ depth g₁ g₀ stamped corrected debt
  have load:op.count≤Burn.horizon epoch.vac+2:=by rw [count,cap]; unfold Burn.horizon; omega
  have fits:grade≤Burn.horizon epoch.vac+1:=by rw [cap]; unfold Burn.horizon; omega
  have fee:0≤Ω⁻¹:=inv_nonneg.mpr (by linarith)
  have paid:=WilsonCoherentMayerMutationIntake.original (R:=R) (hk:=high) (D:=root) (Q:=seat) (π:=π) (Γ:=Γ) (Ψ:=H)
    (course:=course) (books:=books) (hi:=start) (cut:=before) (op:=op) (lesson:=lesson) (ahead:=forecast)
    (actors:=actors D) (M:=X) (w:=weights) (grades:=fun _=>t) (order:=grade) (shelf:=v) (voter:=voter) (cost:=Ω⁻¹)
    (pieces:=fun z=>(nulls D z).restrictScalars ℝ) (Z:=incoming) (rent:=(β̂ (m+1))^(-(grade:ℝ))) (Y:=out)
    pass month hospital story load narrow fits fee hG gain unit εpos (le_trans openDate start)
  refine ⟨paid.2.1,paid.2.2.1,paid.2.2.2.1,?_⟩
  intro x Q₁ u₁ o₁ orders₁ μ₁ D₁
  have initial:(Tint.Patrol.picture X incoming).density x=((ActualOriginalQInput.input Q D u η orders hG N before).leaf
      (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)).density:=funext (enter x)
  have eqn:=(congrArg (LocalComparison.actualPush R.family N p m) initial).symm.trans (paid.1 x)
  exact WilsonCoherentMayerSecondFiling.arrived (N:=N) (R:=R) (j:=i) (per:=p) Q₁ D₁ u₁ μ₁ orders₁
    before.le _ ((Tint.Patrol.picture stamped corrected).density x) eqn

end YM.Integration.WilsonCoherentMayerCloseCampus
