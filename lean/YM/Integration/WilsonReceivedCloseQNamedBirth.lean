import YM.Integration.WilsonReceivedCloseQOpeningPrice
import YM.Integration.WilsonReceivedCloseQCalendar
import YM.Integration.WilsonReceivedFirstQEconomy
import YM.Integration.WilsonOriginalCalibratedQCoveredTrail

/-! Retain the independently named two-birth Q program together with its actual measured entrance.
The ultraviolet cutoff is arbitrary. All copies use the very same pupil, old wallet and fresh source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseQNamedBirth
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
  (u : V → MS.Rake.Label B) (μ : ℝ) (extra : V → ℕ)
  {φ : ℕ → ℕ} (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income : WilsonMovingMentorRootRadius.Income («M»:=R.metals) D φ R.alloy.delay)
  (K : ℕ)
local notation "free" => (fun _ : V => (1:ℝ))
local notation "freePos" => (fun _ : V => zero_lt_one (α:=ℝ))
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
  (upperClock : ℝ) (upperExtra : V→ℕ)
  (upperOrder target order shelf : ℕ) (upperRank : ActualOriginalQLayout.rankCap R upperLabels≤order)
  (upperSites : V→Site (R.family.side ((j+1)+1) per)) (upperOrders : V→ℕ)
local notation "i₁" => (j+1)
local notation "upperFree" => (fun _ : V => (1:ℝ))
local notation "upperPos" => (fun _ : V => zero_lt_one (α:=ℝ))
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

local notation "groupToll" st:max => WilsonReceivedCloseRadiusAccount.registered old fresh upperFree free (st).w
local notation "ut" => ((Classical.choose_spec purchased).2.choose+1)
local notation "ltoll" => max (exponent+1) ((Classical.choose_spec incomeQ).2.choose+1+QuadraticLocal.Spill.Raffle.pad hQ)
local notation "sourceOrder" => max ut ltoll
local notation "upperUnit" => 2*(Classical.choose purchased)*(8:ℝ)^ut
local notation "lowerUnit" => (max (2*factor) (Classical.choose incomeQ))*(4:ℝ)^ltoll
local notation "units" => max 1 (max (upperUnit) (lowerUnit))
local notation "restore" => (budgetR R j)^2*(budgetR R (j+1))^7

local notation "faceFee" n:max => 5*κ*(3:ℝ)^prec*(units)^n
local notation "connectedOrder" a:max q:max => q+(2*sourceOrder+1)*a+1+a
local notation "allMass" => WilsonReceivedLogWindow.original R simple D φ protection mixGrades order shelf k op.count span height angleCap capPos

local notation "d₀" => WilsonReceivedFirstQIncidence.degree ((Classical.choose_spec purchased).2.choose)
  exponent ((Classical.choose_spec incomeQ).2.choose) (QuadraticLocal.Spill.Raffle.pad hQ)
local notation "T₀₀" => WilsonReceivedFirstQIncidence.fee (Classical.choose purchased) factor (Classical.choose incomeQ) 1
local notation "fund₀" => max 1 ((T₀₀)*(8:ℝ)^d₀)
local notation "axes" => Fintype.card V

/-- Both authentic source salaries and the complete actual independent stamped writer live on this post. -/
def Filed (voter:ballot) (start:P₀) : Prop :=
  Scene.Armada M w grades agenda b order op.count shelf ∧
  Scene.Armada (studentOf voter) w grades σ (cost) order op.count shelf ∧
  start.passport=joint ∧ start.modelIndex=(namesOf voter) ∧ HEq start.model (merged voter)

def Birthday (pay:ℕ) : Prop := ∃ (voter:ballot) (start:P₀), Filed (R:=R) (simple:=simple)
    (request:=request) (freshQ:=freshQ) (u:=u) (μ:=μ) (extra:=extra) (D:=D) (hk:=hk) (Q:=Q)
    (π:=π) (Γ:=Γ) (Ψ:=Ψ) (books:=books) (floor:=floor) (cut:=cut) (op:=op) (lesson:=lesson)
    (ahead:=ahead) (income:=income) (way:=way) (ticket:=ticket) (warm:=warm) (education:=education)
    (employment:=employment) (calendar:=calendar) (hospital:=hospital) (pass:=pass)
    (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
    (upperExtra:=upperExtra) (upperOrder:=upperOrder) (order:=order) (shelf:=shelf)
    (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders)
    (old:=old) (fresh:=fresh) (sep:=sep) voter start ∧ start.rent=(g j)^pay ∧
    ∀v∈(old∪fresh), (start.w v)⁻¹ ≤ (fund₀)*((g j)⁻¹)^(2*d₀)

local notation "scaled" p:max => 2*(3:ℝ)^(p+1)
local notation "feeOn" p:max => WilsonReceivedCloseSourceCalendar.reporter_fee R simple
  (show 0 ≤ (scaled p) from mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)) (zero_lt_one:(0:ℝ)<1)

include course path cut simple sep in
theorem original (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (counter:op.count=Fintype.card V) (stage:op.stage=order+1)
    (filing:shelf=reserve) (size:k=order+shelf+Fintype.card V)
    (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (thin:shelf ≤ R.alloy.B.a.clock.J m)
    (upperOK:∀v,upperOrders v≤upperOrder) (lowerOK:∀v,orders v≤K)
    (lowerRank:ActualOriginalQLayout.rankCap R u≤order) (marked:gradeTotal old grades tQ ≤ shelf)
    (pay shape:ℕ) {cap:ℝ} (cn:0≤cap) (needed:prec=pay+1)
    (dates:WilsonReceivedCloseQCalendar.Window R simple request freshQ u μ extra D income K (k:=k) Q books
      ahead way ticket warm education employment calendar hospital pass upperJ upperQ upperLabels upperClock
      upperExtra upperOrder target order shelf upperRank old protection prec span deep aged height angleCap capPos
      (zero_lt_one:(0:ℝ)<1) shape axes pay cn (zero_lt_one:(0:ℝ)<1) m j)
    (loss:(eventually_atTop.mp (feeOn pay)).choose ≤ j)
    (close:PaceR.Close R shape cap m j) :
    Birthday (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ) (u:=u) (μ:=μ) (extra:=extra)
      (D:=D) (income:=income) (K:=K) (hk:=hk) (Q:=Q) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (books:=books)
      (floor:=floor) (cut:=cut) (op:=op) (lesson:=lesson) (ahead:=ahead) (way:=way) (ticket:=ticket)
      (warm:=warm) (education:=education) (employment:=employment) (calendar:=calendar) (hospital:=hospital)
      (pass:=pass) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
      (upperExtra:=upperExtra) (upperOrder:=upperOrder) (order:=order) (shelf:=shelf)
      (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders)
      (old:=old) (fresh:=fresh) (sep:=sep) pay := by
  have countFit:op.count ≤ depth := by unfold Burn.horizon;omega
  have fitOrder:order ≤ Burn.horizon k+1 := by unfold Burn.horizon;omega
  have roomOrder:order+shelf ≤ depth := by unfold Burn.horizon;omega
  have fitNext := thin.trans ((A).fits.mono floor)
  let zeroTest:Wallet A₂ := WilsonMixedTestTableau.pair actors freshA
    (fun v=>⟨0,WilsonOriginalMixedTestTableau.zero upperDatum v⟩) (fun v=>⟨0,WilsonOriginalMixedTestTableau.zero datum v⟩)
  have offered := WilsonOriginalCalibratedQPost.prepaid
      (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ) (u:=u) (μ:=μ) (extra:=extra) («free»:=free)
      (D:=D) (income:=income) (K:=K) («freePos»:=freePos) (hk:=hk) (Q:=Q) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (course:=course)
      (path:=path) (books:=books) (floor:=floor) (cut:=cut) (op:=op) (lesson:=lesson) (ahead:=ahead)
      (way:=way) (ticket:=ticket) (warm:=warm) (education:=education) (employment:=employment)
      (calendar:=calendar) (hospital:=hospital) (pass:=pass) (upperJ:=upperJ) (upperQ:=upperQ)
      (upperLabels:=upperLabels) (upperClock:=upperClock) (upperExtra:=upperExtra) («upperFree»:=upperFree)
      («upperPos»:=upperPos) (upperOrder:=upperOrder) (target:=target) (order:=order) (shelf:=shelf)
      (upperRank:=upperRank) (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites)
      (orders:=orders) (old:=old) (fresh:=fresh) (sep:=sep) (q:=0) (allow:=(zero_lt_one : (0:ℝ)<1))
      scroll chamber month counter stage filing size dates.upper upperOK top countFit fitNext fitOrder
      roomOrder dates.fresh dates.birth Ω₀ (budget_pos R) (min_le_right _ _) lowerOK lowerRank counter.ge marked zeroTest le_rfl
  dsimp only at offered
  obtain ⟨voter,before,earn,jointRadius,h,lesson₂,vote,h₁,hmax,small,wOld,wNew,issue⟩ := offered
  have gBand := (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple shape cap)).choose_spec
    j dates.clock m floor close N per (nextCut).le
  obtain ⟨gj,small⟩ := (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec
    j dates.cool N per (nextCut).le
  have outer := gBand ((j+1)+1) (floor.trans (by omega)) (by omega)
  obtain ⟨start,_,_,passport,index,_,whole,_,radii,_,rent,_⟩ :=
    issue ((g j)^pay) (pow_pos gj _) (pow_le_one₀ gj.le (by linarith only [small,gj]))
  have quoted:=WilsonMovingMentorPagePrice.at_date R books ahead employment calendar (j+1) op
    (Oak.era R hk D Q π Γ hi op lesson) order shelf (fitNext.trans ((A).fits.mono (Nat.le_succ j))) stage.ge countFit
  have wall:4≤elected ∧ elected≤budgetR R (j+1) := ⟨quoted.2.1,quoted.2.2.1⟩
  have stamp:=WilsonReceivedMeasuredStampPrice.original R hk D Q π Γ Ψ course books hi cut op lesson ahead
    actors M order shelf voter pass hospital (fitNext.trans ((A).fits.mono (Nat.le_succ j))) countFit simple prec
    (by omega) (by omega) (zero_lt_one:(0:ℝ)<1) (dates.stamp.trans (Nat.add_le_add_right floor 1))
    (Push.AbsoluteSums.budget_nonneg (before.suggests 0)) le_rfl
    (Real.rpow_nonneg (zero_le_one.trans ((A).fits.delayed ((j+1)+1)).le) (-(order:ℝ)))
  have oldBill := (eventually_atTop.mp (WilsonReceivedCloseCalibratedBudget.original R simple prec
    (zero_lt_one:(0:ℝ)<1))).choose_spec j dates.rent N per (nextCut).le order (by omega)
  have epos:=Real.rpow_nonneg (zero_le_one.trans ((A).fits.delayed ((j+1)+1)).le) (-(order:ℝ))
  have bi : bill ≤ 2*(3*g j)^(pay+1) := by
    rw [←needed]
    have uv:upperG^prec ≤ (3*g j)^prec := pow_le_pow_left₀ outer.1.le outer.2 prec
    have oldPaid:8*elected*e≤(3*g j)^prec := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left wall.2 (by norm_num : (0:ℝ)≤8)) epos).trans (by simpa only [one_mul] using oldBill)
    have charged:bill ≤ 8*elected*e + upperG^prec := by simpa only [one_mul] using stamp
    linarith only [charged,uv,oldPaid]
  refine ⟨voter,start,⟨before,earn,passport,index,whole⟩,?_,?_⟩
  · rw [rent]
    exact WilsonReceivedCloseQOpeningPrice.demand h₁ gj.le bi
      ((eventually_atTop.mp (feeOn pay)).choose_spec j loss N per (nextCut).le)
  · intro v member
    let heat := (A).clock.hatBeta ((j+1)+1)
    have low:1≤xβ := ((A).fits.delayed _).le
    have rise:xβ≤heat := WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le (Nat.le_succ (j+1))
    have capUpper := wall.2.trans (WilsonReceivedCloseQOpeningPrice.page R (j+1))
    have capLower := (WilsonReceivedCloseQOpeningPrice.page R j).trans rise
    obtain ⟨rebatePrice,harder⟩:=WilsonReceivedFirstQEconomy.original R hk D Q π Γ Ψ course books hi cut op lesson ahead
      actors M order shelf voter scroll chamber month pass hospital fitOrder (fitNext.trans ((A).fits.mono (Nat.le_succ j)))
      countFit simple prec (by omega) (by omega) (zero_lt_one:(0:ℝ)<1) (dates.stamp.trans (Nat.add_le_add_right floor 1))
      capUpper (outer.2.trans small)
    let oneMark:(Stock.census V).Mode:=⟨{v},Finset.mem_univ _⟩
    have ok:oneMark.val⊆old∪fresh := Finset.singleton_subset_iff.mpr member
    have sale:=WilsonReceivedFirstQIncidence.priced oneMark old fresh ok upperFree free jointRadius upperPos freePos
      low rise (Classical.choose_spec purchased).1 (Classical.choose_spec offer).1 (Classical.choose_spec incomeQ).1
      (budget_pos R) capLower ((by norm_num:(1:ℝ)≤4).trans wall.1) capUpper rebatePrice h₁
      (harder h hmax) (zero_lt_one:(0:ℝ)<1) wOld wNew
    have f₀:0<T₀₀ := by
      unfold WilsonReceivedFirstQIncidence.fee
      have z:(0:ℝ)<Classical.choose purchased := zero_lt_one.trans_le (Classical.choose_spec purchased).1
      positivity
    have hpos:0<heat:=zero_lt_one.trans_le (low.trans rise)
    have enrolledToll:1/((T₀₀)*heat^d₀) ≤ start.w v := by
      rw [radii]
      simpa only [oneMark,Poly.toll,Finset.prod_singleton,Finset.card_singleton,min_self,pow_one] using sale
    have guard:=WilsonReceivedCloseQOpeningPrice.radius d₀ ((one_div_pos.mpr (mul_pos f₀ (pow_pos hpos _))).trans_le enrolledToll) f₀ hpos gj
      (WilsonReceivedCloseQOpeningPrice.two_upper R simple (nextCut).le dates.nextHat) enrolledToll
    exact guard.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (inv_nonneg.mpr gj.le) _))

end YM.Integration.WilsonReceivedCloseQNamedBirth
