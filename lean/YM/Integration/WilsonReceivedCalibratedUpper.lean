import YM.Integration.WilsonOriginalProjectedCurvaturePassage

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCalibratedUpper
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

open QuadraticLocal.Advent WilsonOriginalProjectedCurvatureTableau
include income way ticket posted active calendar hospital education pass
/-- The funded original curvature appointment exposes the before-field and every compulsory
operand for the next signed reading on this same course. -/
theorem original (K grade q target:ℕ) (ranked:rank ≤ grade) (positive:∀j,0<w j) {ε:ℝ} (εpos:0<ε):
    ∃ C:ℝ,1 ≤ C ∧ ∃ b:ℕ,∀ᶠ m:ℕ in atTop,
    ∀ (op:Mentor.Opportunity (J₀ (m+1)) (J₀ m))
      (epoch:Mentor.Epoch root R.rolls (J₀ (m+1)) (J₀ m) op),
    op.count=h → op.stage=grade+1 → epoch.vac=grade+v+h →
    let Ω:=Mentor.Cruise.Semester.expense root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
    4 ≤ Ω ∧ Ω ≤ (β̂ (m+1))^(Beaming.grain (J₀ m)) ∧
    ∀ (N p:ℕ) (o:V→Site (R.family.side (m+1) p)) (orders:V→ℕ), (∀i,orders i ≤ K) →
      ∀ (before:m<N) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (H:(s:ℕ)→Rep G (R.family.side s p))
      (first:ℕ) (start:first ≤ m) (_course:Concourse R.alloy R.kit R.T π Γ first N p epoch.vac H)
      (hk:Burn.horizon epoch.vac+2 ≤ J₀ first)
      (_lesson:Oak.Lesson (N:=N) R hk root seat π Γ start),
      Topline (H N) (R.family.path.levels.clock.forcedAllowance N) →
      let D:=ActualOriginalQPointSetup.pointDatum R J p (m+1) o
      let σ:=Poetry.Agenda.seed root ψ (Burn.horizon (grade+v+h)) (J₀ (m+1))
      let η:=(μ+R.family.S.scale N-R.family.S.scale (m+1))-R.family.S.scale N
      let X:=WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
      let a:=C*(β̂ (m+1))^(b+1)
      let weights:=fun j=>w j/(a*Ω)
      let g:=Coat.gStep (R.family.path.rep N p (m+1)).beta
      (∀ s:(Stock.census V).Mode,Poly.toll weights s*(a*Ω)^s.val.card=Poly.toll w s ∧
        (a*Ω)^s.val.card*g^(q+2*((b+1)*h)+1) ≤ ε*g^q) ∧
      ∃ _signed:∀i,0<weights i, ∃ _voter:Mentor.Cruise.Voter X (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1))) grade op.count op.stage epoch.vac (J₀ m),
      ∃ incoming:Tint.Incoming (paper D u) (H (m+1)) (tastes D) Empty (Stock.census V),
        (∀ (x:tastes D) (U:Config G (R.family.side (m+1) p)),
          (Tint.Patrol.picture X incoming).density x U=
            ((ActualOriginalQInput.input Q D u η orders hG N before).leaf
              (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)).density U) ∧
        Scene.Armada X weights (fun _=>t) (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac)
            (J₀ (m+1))) Ω⁻¹ grade op.count v ∧
        Affinity.Taut (paper D u).support (actors D)
          (fun i=>(nulls D i).restrictScalars ℝ) incoming.old ∧
        Affinity.Crown (paper D u).support (actors D)
          (fun i=>(nulls D i).restrictScalars ℝ) incoming.hard ∧
        (∀ radius budget,incoming.old.Paid weights budget radius 0) ∧
        incoming.hard.Paid weights (H (m+1)).p.B (H (m+1)).p.supportExponent
          ((β̂ (m+1))^(-(target:ℝ))*forcedDivisor R.family (m+1)) ∧
        incoming.hard.Paid weights (H (m+1)).p.B (H (m+1)).p.supportExponent 1 := by
  obtain ⟨C,hC,b,funded⟩:=WilsonCoherentMayerMeasuredEarnings.original R hG J Q u μ extra w root
    seat way ticket posted income books forecast education active calendar hospital pass
    K grade q target ranked positive εpos
  let horizon:=Burn.horizon (grade+v+h)
  let minimum:=horizon+rank+v+h+(target+Spill.Raffle.pad (rank+v+1)*h)
  let firstRow:=WilsonOriginalProjectedCurvatureScheduledField.earliest R u
  have next:Filter.Tendsto (fun m:ℕ=>m+1) atTop atTop:=tendsto_add_atTop_nat 1
  refine ⟨C,hC,b,?_⟩
  filter_upwards [funded,R.alloy.B.a.fits.deep.eventually_ge_atTop v,
    (R.alloy.B.a.fits.deep.comp next).eventually_ge_atTop minimum,next.eventually_ge_atTop firstRow]
    with m purchased width qualified high
  intro op epoch count level vac Ω
  obtain ⟨large,roof,booked⟩:=purchased op epoch count level vac
  refine ⟨large,roof,?_⟩
  intro N p o orders capped before π Γ H first start course hk lesson top D σ η X a weights g
  obtain ⟨restore,signed,voter,seated,_⟩:=booked N p o orders capped before π Γ H first start
    course lesson.entry lesson.studied lesson.ticket top
  have one:1≤Ω:=by linarith
  have rows:Scene.Armada X weights (fun _=>t) σ Ω⁻¹ rank h v:=by simpa only [vac] using seated
  have installed:Scene.Armada X weights (fun _=>t) σ 1 rank h v:=
    { toMinistry:=rows.toMinistry,positive:=rows.positive,purchases:=rows.purchases,honor:=rows.honor
      suggests:=fun x=>Push.AbsoluteSums.budget_loosen (rows.suggests x) (inv_le_one_of_one_le₀ one) }
  have ready (s:Slot u):R.family.ref s.2.size ≤ m+1:=
    (Finset.le_sup (f:=fun s:Slot u=>R.family.ref s.2.size) (Finset.mem_univ s)).trans high
  change horizon+rank+v+h+(target+Spill.Raffle.pad (rank+v+1)*h) ≤ J₀ (m+1) at qualified
  have selected:horizon ≤ J₀ (m+1):=by omega
  obtain ⟨incoming,taut,crown,old,hard,read⟩:=WilsonOriginalProjectedCurvatureAttunedDate.measured
    (R:=R) (Q:=Q) (target:=target) (D:=D) (u:=u) (μ:=η) (orders:=orders) (extra:=extra)
    (hG:=hG) (ready:=ready) (root:=root) (seat:=seat) (way:=way) (ticket:=ticket) (posted:=posted)
    (story:=course) (start:=Nat.le_succ_of_le start) (reached:=before) (top:=top) installed selected
    (by omega) (by omega) (by omega) (by omega)
  have step:Scene.Armada X weights (fun _=>t) (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac)
      (J₀ (m+1))) Ω⁻¹ grade op.count v:=
    ⟨⟨fun s=>(seated.quota s).trans count.ge,fun s=>seated.crew s⟩,seated.positive,
     seated.suggests,⟨seated.purchases.spend,fun s=>
      ⟨((seated.purchases.usable s).1).trans ranked,(seated.purchases.usable s).2⟩⟩,seated.honor⟩
  have held:=Graces.glyphBound R.family.path.levels (m+1)
  have at_least:1≤β̂ (m+1):=(R.alloy.B.a.fits.delayed (m+1)).le
  have raised:(β̂ (m+1))^(-(target:ℝ))≤1:=Real.rpow_le_one_of_one_le_of_nonpos at_least
    (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hardOne:=incoming.hard.mono hard ((mul_le_mul_of_nonneg_right raised held.1.le).trans
    ((one_mul _).trans_le held.2))
  exact ⟨restore,signed,voter,incoming,read,step,taut,crown,old,hard,hardOne⟩

end YM.Integration.WilsonReceivedCalibratedUpper
