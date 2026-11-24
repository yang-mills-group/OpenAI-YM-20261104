import YM.Integration.WilsonOriginalProjectedCurvatureOnCard
import YM.Integration.WilsonCoherentMayerPublishedSlip
import YM.Integration.WilsonMovingMentorPagePrice
import YM.Integration.WilsonOriginalPointUnitTest
import YM.Integration.WilsonOriginalProjectedCurvatureScheduledField
import YM.Integration.WilsonOriginalProjectedCurvatureHardDate

/-! Open the actual physical previous gas on the presold Terrace, keeping
the entire charged Q at its independently filed reporting date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerMeasuredEarnings
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

include income way ticket posted active calendar hospital education
/-- The original normalized curvature input, its actual physical course, and every returned signed test
use one allowance chosen at the measured date before either finite regulator. -/
theorem original (K grade q target:ℕ) (ranked:rank ≤ grade) (positive:∀j,0<w j) {ε:ℝ} (εpos:0<ε):
    ∃ C:ℝ,1 ≤ C ∧ ∃ b:ℕ,∀ᶠ m:ℕ in atTop,
    ∀ (op:Mentor.Opportunity (J₀ (m+1)) (J₀ m))
      (epoch:Mentor.Epoch root R.rolls (J₀ (m+1)) (J₀ m) op),
    op.count=h → op.stage=grade+1 → epoch.vac=grade+v+h →
    let Ω:=Mentor.Cruise.Semester.expense root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
    4 ≤ Ω ∧ Ω ≤ (β̂ (m+1))^(Beaming.grain (J₀ m)) ∧
    ∀ (N p:ℕ) (o:V→Site (R.family.side (m+1) p)) (orders:V→ℕ), (∀i,orders i ≤ K) →
      ∀ (before:m<N) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (H:(s:ℕ)→Rep G (R.family.side s p))
      (first:ℕ) (start:first ≤ m) (course:Concourse R.alloy R.kit R.T π Γ first N p epoch.vac H)
      (card:WilsonMovingMentorItinerary.CardAt R root epoch.vac m)
      (journey:PlanV.Journey root R.alloy (N:=N) (m:=m) card), π (m+1)=card.extra →
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
      ∃ signed:∀i,0<weights i, ∃ voter:Mentor.Cruise.Voter X (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1))) grade op.count op.stage epoch.vac (J₀ m),
      let size:=(R.alloy.B.a.S.oneStep m p).exact_size
      let published:=Mentor.Cruise.publish root R.rolls seat R.alloy ψ books op epoch size X grade voter card
      let receipt:=Mentor.Cruise.funded root R.rolls seat R.alloy ψ books op epoch size X grade voter card journey forecast
      let E:=Mentor.Cruise.Semester.figure root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
      Scene.Armada X weights (fun _=>t) (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1))) Ω⁻¹ rank h v ∧
      WilsonRootedKioskOccupiedSlip.Gross (Width.treasured X (Pane.panel R.alloy m size).ratio
        published receipt (H m).p E.afterwards (Coat.gStep (H (m+1)).beta)) weights (H m).p.B
        ((H m).p.supportExponent+1) ((Spill.allOver (H m).p)^E.cap*Ω) ∧
      ∃ incoming:Tint.Incoming (paper D u) (H (m+1)) (tastes D) Empty (Stock.census V),
        incoming.hard.Paid weights (H (m+1)).p.B (H (m+1)).p.supportExponent
          ((β̂ (m+1))^(-(target:ℝ))*forcedDivisor R.family (m+1)) ∧
        (∀ (x:tastes D) (U:Config G (R.family.side (m+1) p)),
          let input:=(ActualOriginalQInput.input Q D u η orders hG N before).leaf
            (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)
          (Tint.Patrol.picture X incoming).density x U=input.density U) ∧
      ∃ sealed:Travel.Seal (Tint.Patrol.picture X incoming) weights 2 1,
        Tint.Campus.Investor.Medal X incoming weights sealed 0 ((Coat.gStep (H (m+1)).beta)^op.stage) ∧
        ∃ Z:Burn.Seed (H (m+1)) (WheelP.M0 epoch.vac 0 (R.alloy.B.a.budget (m+1)) card.extra (H (m+1)).beta),
        Burn.Candor (R.alloy.B.a.budget (m+1)) (H (m+1)).activities (Set.range Z.model)
          (Burn.silver (β̂ (m+1))) (Burn.young (β̂ (m+1)) epoch.vac) ∧
        ∀ y:tastes D, WilsonOriginalProjectedCurvatureCourseNotice.Clause R root seat ψ books pass op epoch card course
          start before X weights signed voter incoming sealed y Z := by
  obtain ⟨C,hC,b,submit⟩:=WilsonOriginalProjectedCurvatureOnCard.original R hG J Q u μ extra w root income
    K grade q positive εpos
  let horizon:=Burn.horizon (grade+v+h)
  let minimum:=horizon+rank+v+h+(target+Spill.Raffle.pad (rank+v+1)*h)
  let firstRow:=WilsonOriginalProjectedCurvatureScheduledField.earliest R u
  have next:Filter.Tendsto (fun m:ℕ=>m+1) atTop atTop:=tendsto_add_atTop_nat 1
  refine ⟨C,hC,b,?_⟩
  filter_upwards [submit,R.alloy.B.a.fits.deep.eventually_ge_atTop v,
    (R.alloy.B.a.fits.deep.comp next).eventually_ge_atTop minimum,next.eventually_ge_atTop firstRow]
    with m booked width qualified high
  intro op epoch count level vac Ω
  have load:op.count ≤ Burn.horizon epoch.vac+2:=by rw [count,vac]; unfold Burn.horizon; omega
  have paid:=WilsonMovingMentorPagePrice.at_date R books forecast active calendar m op epoch grade v width
    (by omega) load
  have large:4 ≤ Ω:=paid.2.1
  have one:1 ≤ Ω:=by linarith
  have roof:Ω ≤ (β̂ (m+1))^(Beaming.grain (J₀ m)):=paid.2.2.1.trans (min_le_right _ _)
  refine ⟨large,roof,?_⟩
  intro N p o orders capped before π Γ H first start course card journey upper top D σ η X a weights g
  obtain ⟨vote₀,rows₀,restore⟩:=booked (vac ▸ card) Ω one roof N p o orders capped before
  have vote:Mentor.Cruise.Voter X (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1))) grade op.count op.stage epoch.vac (J₀ m):=by
    rw [count,level,vac]
    exact vote₀
  have rows:Scene.Armada X weights (fun _=>t) σ Ω⁻¹ rank h v:=rows₀
  have seated:Scene.Armada X weights (fun _=>t) (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1))) Ω⁻¹ rank h v:=by
    rw [vac]; exact rows
  have installed:Scene.Armada X weights (fun _=>t) σ 1 rank h v:=
    { toMinistry:=rows.toMinistry,positive:=rows.positive,purchases:=rows.purchases,honor:=rows.honor
      suggests:=fun x=>Push.AbsoluteSums.budget_loosen (rows.suggests x) (inv_le_one_of_one_le₀ one) }
  have ready (s:Slot u):R.family.ref s.2.size ≤ m+1:=
    (Finset.le_sup (f:=fun s:Slot u=>R.family.ref s.2.size) (Finset.mem_univ s)).trans high
  change horizon+rank+v+h+(target+Spill.Raffle.pad (rank+v+1)*h) ≤ J₀ (m+1) at qualified
  have selected:horizon ≤ J₀ (m+1):=by omega
  obtain ⟨incoming,retained,read⟩:=WilsonOriginalProjectedCurvatureHardDate.measured (R:=R) (Q:=Q) (target:=target)
    (D:=D) (u:=u) (μ:=η) (orders:=orders) (extra:=extra) (hG:=hG) (ready:=ready) (root:=root)
    (seat:=seat) (way:=way) (ticket:=ticket) (posted:=posted) (story:=course) (start:=Nat.le_succ_of_le start)
    (reached:=before) (top:=top) installed selected (by omega) (by omega) (by omega) (by omega)
  obtain ⟨gross,sealed,medal,Z,stamped,_⟩:=WilsonCoherentMayerPublishedSlip.original
    (R:=R) (simple:=hG) (root:=root) (table:=seat) (ψ:=ψ) (books:=books) (pass:=pass)
    (education:=education) (op:=op) (epoch:=epoch) (card:=card) (journey:=journey) (upper:=upper)
    (course:=course) (start:=start) (before:=before) (M:=X) (w:=weights) (positive:=rows.positive)
    (voter:=vote) (input:=incoming) (y:=WilsonOriginalPointModes.unit (ActualRunQlocalNativeTuple.orbit D)) (forecast:=forecast) (hospital:=hospital)
    (vol:=v) (tolls:=fun _=>t) (q:=target) (height:=load) (room:=width) (j:=rank) (k:=h) («v»:=v) (rows:=seated) (jet:=ranked) (crew:=count.ge) (placed:=le_refl v) (retained:=retained)
  refine ⟨restore,rows.positive,vote,seated,gross,incoming,retained,read,sealed,medal,Z,stamped,fun y=>?_⟩
  exact WilsonOriginalProjectedCurvatureCourseNotice.original (R:=R) (simple:=hG) (root:=root) (table:=seat)
    (ψ:=ψ) (books:=books) (pass:=pass) (education:=education) (op:=op) (epoch:=epoch) (card:=card)
    (journey:=journey) (course:=course) (start:=start) (before:=before) (M:=X)
    (w:=weights) (positive:=rows.positive) (voter:=vote) (input:=incoming) (sealed:=sealed) (y:=y) Z

end YM.Integration.WilsonCoherentMayerMeasuredEarnings
