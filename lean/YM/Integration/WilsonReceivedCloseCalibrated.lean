import YM.Integration.WilsonReceivedCloseSlate
import YM.Integration.WilsonReceivedCloseCalibratedBudget
import YM.Integration.WilsonReceivedCloseStamp
import YM.Integration.WilsonMovingMentorPagePrice
import YM.Integration.WilsonOriginalCalibratedQPrepaidPost

/-! Two deposited original curvature cohorts compared with their received finite banks across the Wilson close interval. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseCalibrated
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

variable {G : Gauge} (R : Run G) (simple : G.Simple) {B : MS.Local.Physical.Deck G}
  {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] (request : Request V) (freshQ : MS.Land.Prescription B)
  (u : V → MS.Rake.Label B) (μ : ℝ) (extra : V → ℕ) (free : V → ℝ)
  {φ : ℕ → ℕ} (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
  (K : ℕ) (freePos : ∀ v, 0 < free v)
local notation "offer" => WilsonOriginalMixedFiniteVoter.original R request freshQ u μ extra free D income simple K 0 freePos (zero_lt_one : (0:ℝ)<1)
local notation "factor" => Classical.choose offer
local notation "exponent" => (Classical.choose_spec offer).2.choose

variable {m j N per k : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (Q : D.Tab R.rolls) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
  (Ψ : ∀ l, RG.Rep G (R.family.side l per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
  (books : Mentor.Offices.Books D R.rolls Q φ) (floor : m ≤ j) (cut : j+1 < N)
local notation "depth" => Burn.horizon k+2
local notation "T₀" => AllOrder.Floe.Step.tape depth
variable (op : Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson : Lesson (N:=N) R hk D Q π Γ (floor.trans (Nat.le_succ j))) (ahead : Mentor.Forecast D R.rolls Q φ books)
  (way : WayStation R.kit) (ticket : TicketP R.alloy R.kit D Q)
  (warm : QuadraticLocal.Spill.Raffle.Warm G D R.alloy.delay φ)
  (education : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
  (employment : ∀ d,MintClock.Employment D φ d (R.rolls.L d))
  (calendar : MintClock.Regency D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (pass : Pass D Q R.alloy R.kit)
  (upperJ : Request V) (upperQ : MS.Land.Prescription B) (upperLabels : V→MS.Rake.Label B)
  (upperClock : ℝ) (upperExtra : V→ℕ) (upperFree : V→ℝ) (upperPos : ∀ a,0<upperFree a)
  (upperOrder target order shelf : ℕ) (upperRank : ActualOriginalQLayout.rankCap R upperLabels≤order)
  (upperSites : V→Site (R.family.side ((j+1)+1) per)) (upperOrders : V→ℕ)
local notation "i₁" => (j+1)
local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "A" => R.alloy.B.a
local notation "elected" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "b" => (elected)⁻¹
local notation "agenda" => QuadraticLocal.Poetry.Agenda.seed D φ (Burn.horizon k) ((A).clock.J ((j+1)+1))
local notation "upperDatum" => ActualOriginalQPointSetup.pointDatum R upperJ per ((j+1)+1) upperSites
local notation "upperFee" => (upperClock+R.family.S.scale N-R.family.S.scale ((j+1)+1))-R.family.S.scale N
local notation "actors" => WilsonOriginalProjectedCurvatureTableau.actors upperDatum
local notation "pieces₀" => (fun v=>(WilsonOriginalProjectedCurvatureTableau.nulls upperDatum v).restrictScalars ℝ)
local notation "M" => WilsonOriginalProjectedCurvatureLamps.cohort upperQ upperDatum upperLabels upperFee upperOrders N agenda upperExtra
local notation "grades" => (fun _ : V => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) upperLabels)
local notation "reserve" => (Fintype.card V*WilsonOriginalProjectedCurvatureLoan.toll (R:=R) upperLabels)
local notation "purchased" => WilsonReceivedCalibratedUpper.prepaid R simple upperJ upperQ upperLabels upperClock
  upperExtra upperFree D Q way ticket warm income books ahead education employment calendar hospital pass upperOrder upperPos
local notation "upperBank" => (Classical.choose_spec purchased).2.choose_spec order 0 target upperRank (zero_lt_one : (0:ℝ)<1)
local notation "w" => (fun v=>upperFree v/((Classical.choose purchased)*((A).clock.hatBeta ((j+1)+1))^((Classical.choose_spec purchased).2.choose+1)*(elected)))
local notation "testPass" => paper upperDatum upperLabels
local notation "zeroA" => WilsonOriginalMixedTestTableau.zero upperDatum
local notation "ballot" => Mentor.Cruise.Voter M agenda order op.count op.stage k ((A).clock.J (j+1))
local notation "oldRows" ν => Mutation.stamp (Oak.student (m:=m) (i:=j+1) (n:=per) (N:=N) (k:=k) R hk D Q π Γ books hi op lesson ahead actors M order ν)
  (Γ (j+1)) (Oak.grade0 R hk D Q π Γ hi lesson) depth order
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "fig" => Oak.figureReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead order shelf
local notation "rebate" => Oak.rebate R hk D Q π Γ (floor.trans (Nat.le_succ j)) op lesson
local notation "page" => WilsonMovingMentorPageRefund.cap R j
local notation "tQ" => (fun _ : V => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u)
variable (sites : V → Site (R.family.side (j+1) per)) (orders : V → ℕ)
local notation "datum" => ActualOriginalQPointSetup.pointDatum R request per (j+1) sites
local notation "η" => (μ+R.family.S.scale N-R.family.S.scale (j+1))-R.family.S.scale N
local notation "newRows" => WilsonOriginalProjectedCurvatureLamps.cohort freshQ datum u η orders N σ extra

variable (old fresh:Finset V) (sep:Disjoint old fresh)
local notation "freshA" => WilsonOriginalProjectedCurvatureTableau.actors datum
local notation "Knew" => (fun v=>(WilsonOriginalProjectedCurvatureTableau.nulls datum v).restrictScalars ℝ)
local notation "A₂" => WilsonMixedTestTableau.actors actors freshA
local notation "l" => WilsonMixedTestTableau.left actors freshA old zeroA
local notation "rTest" => WilsonMixedTestTableau.right actors freshA fresh (WilsonOriginalMixedTestTableau.zero datum)
local notation "mixGrades" => choice old grades tQ
local notation "sheet" => Pane.panel R.alloy (j+1) (R.alloy.B.a.S.oneStep (j+1) per).exact_size
local notation "xβ" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "paidScale" => factor*xβ^(exponent+1)
local notation "hQ" => ActualOriginalQLayout.rankCap R u+Fintype.card V*WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u+1
local notation "risk" => (xβ^QuadraticLocal.Spill.Raffle.pad hQ)
local notation "incomeQ" => WilsonOriginalFreshQAtReceivedDate.prepaid R simple request freshQ u μ extra free D income warm K freePos
local notation "entrance" => (Classical.choose_spec incomeQ).2.choose_spec
local notation "m₀" => WilsonOriginalJointQWallet.firstBirth R simple request freshQ u μ extra free D income K freePos warm
local notation "hβ" => R.alloy.B.a.clock.J (j+1)


local notation "nextCut" => (Nat.lt_trans (Nat.lt_succ_self j) cut)
local notation "H" => Ψ (j+1)
local notation "w₀" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "vac" => Burn.young ((A).clock.hatBeta ((j+1)+1)) k
local notation "e" => (((A).clock.hatBeta ((j+1)+1))^(-(order:ℝ)))
local notation "ratio" => (sheet).ratio
local notation "cost" => (fig).produce (ratio).count*b
local notation "spent" => (fig).hitPrice G (ratio).count (Ψ ((j+1)+1)).p (H).p b e vac w₀
local notation "fee" => QuadraticLocal.Earn.Invoice.price (H).p (fig).mist (order+shelf+1) op.count ((H).p.supportExponent+1+1) (fig).limitC G
local notation "bill" => (fig).fidelity*fee*(cost)+spent
local notation "raw" => ActualOriginalQInput.input upperQ upperDatum upperLabels upperFee upperOrders simple N (Nat.succ_le_of_lt cut)
local notation "prior" => fun x=> (sheet).push (Ψ ((j+1)+1)).beta (fun U=>((raw).leaf
  (testInclusion (ActualRunQlocalNativeTuple.orbit upperDatum) (l x))).density U)
local notation "physical" => fun x U=>Poly.pass (MergeProof.Accent.Mach (Stock.census V) (fun v =>
  ActualRunQlocalNativeTuple.reader datum v (testInclusion (ActualRunQlocalNativeTuple.orbit datum) (rTest x) v) *
    ActualOriginalCalibratedColumns.weightedObservable R B freshQ (u v) η (R.family.side i₁ per)
      (ActualRunQlocalNativeTuple.root datum v) U (orders v))) * (prior x U)
local notation "inputField " I => fun x U=>Poly.pass (MergeProof.Accent.Mach (Stock.census V) (fun v =>
  ActualRunQlocalNativeTuple.reader datum v (testInclusion (ActualRunQlocalNativeTuple.orbit datum) (rTest x) v) *
    ActualOriginalCalibratedColumns.weightedObservable R B freshQ (u v) η (R.family.side i₁ per)
      (ActualRunQlocalNativeTuple.root datum v) U (orders v))) * ((sheet).push (Ψ ((j+1)+1)).beta ((QuadraticLocal.Tint.Patrol.picture M I).density (l x)) U)
local notation "move" => (R.family.path.levels.clock.op j per)
open QuadraticLocal.Affinity VowsR QuadraticLocal.Mentor


local notation "home" => (testPass).coarser (sheet).ratio
local notation "joint" => WilsonMixedPassportRows.passport (WilsonMixedPassportRows.owner home (paper datum u) old)
local notation "K₂" => WilsonMixedTestTableau.pieces pieces₀ Knew
local notation "merged" ν => WilsonMixedFaceLog.routed (oldRows ν) newRows old fresh sep l rTest
local notation "namesOf" ν => (WilsonMixedPassportRows.Face (oldRows ν) old ⊕ WilsonMixedPassportRows.Face newRows fresh)
local notation "spare" => QuadraticLocal.Willow.haloSlack ((A).budget (j+1)).B
local notation "df" => LocalComparison.forcedDivisor R.family (j+1)
local notation "wage" => ((H).p.supportExponent+1+1)

local notation "studentOf" ν => Oak.student (m:=m) (i:=j+1) (n:=per) (N:=N) (k:=k) R hk D Q π Γ books hi op lesson ahead actors M order ν

local notation "g" => regulatorRun R.family N per
local notation "upperG" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
local notation "Ω₀" => budgetR R j
variable
  (protection : ∀ x k : ℕ, k ≤ x → ∀ β : ℝ, R.alloy.delay.betaEntry x ≤ β →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2) ≤ β)
  (prec span : ℕ) (deep : 2*(prec+1)+8 ≤ order) (aged : prec+4 ≤ 3*k+2)
  (height angleCap : ℝ) (capPos : 0 ≤ angleCap) {κ : ℝ} (kp : 0 < κ)
local notation "hearing" => WilsonReceivedCloseSlate.opens R D mixGrades order shelf op.count simple protection
  prec span deep aged height angleCap capPos kp
local notation "P₀" => Post (N:=N) R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf op.count j floor physical
local notation "paid" st:max arity':max width':max price':max => WilsonReceivedCloseSlate.Paid R hk D Q π Γ Ψ books
  ahead A₂ K₂ mixGrades order shelf op.count floor physical st nextCut arity' span height angleCap width' price'

include course path cut simple sep in
theorem original (scroll:VowsR.LawScroll G φ)
    (chamber:VowsR.Chamber scroll R.kit D Q books) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (upperCount:op.count=Fintype.card V) (upperStage:op.stage=order+1)
    (heldShelf:shelf=reserve) (fundedGrade:k=order+shelf+Fintype.card V)
    (qualified:(eventually_atTop.mp upperBank).choose≤j+1) (within:∀a,upperOrders a≤upperOrder)
    (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (load:op.count ≤ depth) (narrow:shelf ≤ R.alloy.B.a.clock.J j) (fits:order ≤ Burn.horizon k+1)
    (packed:order+shelf ≤ depth) (late:WilsonOriginalMixedStampedFinite.firstDate R simple request freshQ u μ extra free D income K 0 freePos (zero_lt_one : (0:ℝ)<1) ≤ j)
    (funded:m₀ ≤ j+1) (ordersOK:∀v,orders v ≤ K)
    (rank:ActualOriginalQLayout.rankCap R u ≤ order) (count:Fintype.card V ≤ op.count)
    (level:gradeTotal old grades tQ ≤ shelf)
    (x : Wallet A₂)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (thin : shelf ≤ R.alloy.B.a.clock.J m) (unit : κ ≤ 1) (stage : k ≤ R.alloy.B.a.clock.J m)
    (openRead : (eventually_atTop.mp hearing).choose ≤ m)
    (lateStamp : WilsonReceivedMeasuredStampPrice.opening R simple prec order k (by omega) (by omega) kp ≤ m+1)
    (degree a : ℕ) {cap loss : ℝ} (cn : 0 ≤ cap) (slack : 0 < loss)
    (ready : WilsonReceivedCloseSignedPrice.opening R simple degree a prec op.count cn slack kp.le ≤ j)
    (clock : (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose ≤ j)
    (runRate : (eventually_atTop.mp (WilsonReceivedCloseCalibratedBudget.original R simple prec kp)).choose ≤ j)
    (close : PaceR.Close R degree cap m j) :
    ∃ (voter : ballot) (jointRadius : V → ℝ) (h : ℝ) (start : P₀),
      start.modelIndex=(namesOf voter) ∧
      (∀ y, Air.craft start.model (fun d=>(start.model d).paint y) mixGrades (π (j+1)) T₀ =
        Air.craft (merged voter) (fun d=>((merged voter) d).paint y) mixGrades (π (j+1)) T₀) ∧
      4 ≤ elected ∧ elected ≤ budgetR R (j+1) ∧ rebate*cost ≤ budgetR R (j+1) ∧
      1 ≤ h ∧ h ≤ max (max 1 (bill)) (elected^5+1) ∧
      (∀ a∈old,jointRadius a=w a/(max 1 (Ω₀*(rebate*cost)))/2) ∧
      (∀ a∈fresh,jointRadius a=min (free a/(paidScale*Ω₀)/2)
        (free a/((Classical.choose incomeQ*xβ^((Classical.choose_spec incomeQ).2.choose+1))*risk))) ∧
      start.w=QuadraticLocal.Stoop.radius jointRadius h ∧
      paid start a start.w (fun _ => (g j)^(-loss)*(5*κ*(3*g j)^prec)) := by
  have offered := WilsonOriginalCalibratedQPost.prepaid
      (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ) (u:=u) (μ:=μ) (extra:=extra) (free:=free)
      (D:=D) (income:=income) (K:=K) (freePos:=freePos) (hk:=hk) (Q:=Q) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (course:=course)
      (path:=path) (books:=books) (floor:=floor) (cut:=cut) (op:=op) (lesson:=lesson) (ahead:=ahead)
      (way:=way) (ticket:=ticket) (warm:=warm) (education:=education) (employment:=employment)
      (calendar:=calendar) (hospital:=hospital) (pass:=pass) (upperJ:=upperJ) (upperQ:=upperQ)
      (upperLabels:=upperLabels) (upperClock:=upperClock) (upperExtra:=upperExtra) (upperFree:=upperFree)
      (upperPos:=upperPos) (upperOrder:=upperOrder) (target:=target) (order:=order) (shelf:=shelf)
      (upperRank:=upperRank) (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites)
      (orders:=orders) (old:=old) (fresh:=fresh) (sep:=sep) (q:=0) (allow:=(zero_lt_one : (0:ℝ)<1))
      scroll chamber month upperCount upperStage heldShelf fundedGrade qualified within top load narrow fits
      packed late funded Ω₀ (budget_pos R) (min_le_right _ _) ordersOK rank count level x le_rfl
  dsimp only at offered
  obtain ⟨voter,before,earn,jointRadius,h,lesson₂,vote,h₁,hmax,small,wOld,wNew,issue⟩ := offered
  have costed := WilsonReceivedMeasuredStampPrice.original R hk D Q π Γ Ψ course books hi cut op lesson ahead
    actors M order shelf voter pass hospital (narrow.trans ((A).fits.mono (Nat.le_succ j))) load simple prec
    (by omega) (by omega) kp (lateStamp.trans (Nat.add_le_add_right floor 1))
    (Push.AbsoluteSums.budget_nonneg (before.suggests 0)) le_rfl
    (Real.rpow_nonneg (zero_le_one.trans ((A).fits.delayed ((j+1)+1)).le) (-(order:ℝ)))
  have band := (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose_spec
    j clock m floor close N per (nextCut).le
  have gj := (band j floor (nextCut).le).1
  have gu := (band ((j+1)+1) (by omega) (by omega)).2
  let τ := min 1 (κ*(3*g j)^prec)
  have τp : 0<τ := lt_min zero_lt_one (mul_pos kp (pow_pos (by positivity) _))
  obtain ⟨start,_op,_lesson,_passport,index,air,_model,_voter,radius,_cost,rent,_quiet⟩ :=
    issue τ τp (min_le_left _ _)
  have pagePaid := WilsonMovingMentorPagePrice.at_date R books ahead employment calendar (j+1) op
    (Oak.era R hk D Q π Γ hi op lesson) order shelf (narrow.trans ((A).fits.mono (Nat.le_succ j))) upperStage.ge load
  have wall : 4 ≤ elected ∧ elected ≤ budgetR R (j+1) := ⟨pagePaid.2.1,pagePaid.2.2.1⟩
  have stamp := WilsonReceivedCloseStamp.original R hk D Q π Γ Ψ course books hi cut op lesson ahead
    actors M order shelf voter scroll chamber month pass hospital fits (narrow.trans ((A).fits.mono (Nat.le_succ j)))
    load (Push.AbsoluteSums.budget_nonneg (before.suggests 0)) le_rfl
  refine ⟨voter,jointRadius,h,start,index,air,wall.1,wall.2,stamp,h₁,hmax,wOld,wNew,radius,?_⟩
  have charge : (bill) ≤ 8*elected*e+κ*(3*g j)^prec := by
    refine costed.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ kp.le))
    exact pow_le_pow_left₀ ((band ((j+1)+1) (by omega) (by omega)).1.le) gu _
  have hpos : 0<h := zero_lt_one.trans_le h₁
  have clean : 0≤8*elected*e+κ*(3*g j)^prec := by
    have payNonneg : 0 ≤ elected := by linarith only [wall.1]
    have young := Real.rpow_nonneg (zero_le_one.trans ((A).fits.delayed ((j+1)+1)).le) (-(order:ℝ))
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) payNonneg) young)
      (mul_nonneg kp.le (pow_nonneg (by positivity) _))
  have startBill : start.rent ≤ 8*elected*e + 2*κ*(3*g j)^prec := by
    rw [rent]
    apply max_le
    · have pay := (mul_le_mul_of_nonneg_left charge (inv_nonneg.mpr hpos.le)).trans
        (mul_le_of_le_one_left clean (inv_le_one_of_one_le₀ h₁))
      linarith only [pay, mul_nonneg kp.le (pow_nonneg (by positivity : 0 ≤ 3*g j) prec)]
    · have pick : τ ≤ κ*(3*g j)^prec := min_le_right _ _
      linarith only [pick,clean]
  have tail := (eventually_atTop.mp (WilsonReceivedCloseCalibratedBudget.original R simple prec kp)).choose_spec
    j runRate N per (nextCut).le order (by omega)
  have originalHead : 8*elected*e ≤ κ*(3*g j)^prec := (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left wall.2 (by norm_num: (0:ℝ)≤8))
    (Real.rpow_nonneg (zero_le_one.trans ((A).fits.delayed ((j+1)+1)).le) (-(order:ℝ)))).trans tail
  have arrival := WilsonReceivedCloseSlate.original R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order
    shelf op.count floor physical simple protection prec span deep aged height angleCap capPos kp
    start course path nextCut pass scroll chamber month hospital fund fits thin load packed unit stage
    ((eventually_atTop.mp hearing).choose_spec m openRead) lateStamp x degree a cn slack ready close
  apply WilsonReceivedCloseSlate.reprice R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf op.count
    floor physical start nextCut a span height angleCap (c:=fun _=>1) arrival
  intro s hs live
  refine ⟨zero_le_one,le_of_eq (one_mul _).symm,?_⟩
  rw [one_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg gj.le _)
  linarith only [startBill,originalHead]

end YM.Integration.WilsonReceivedCloseCalibrated
