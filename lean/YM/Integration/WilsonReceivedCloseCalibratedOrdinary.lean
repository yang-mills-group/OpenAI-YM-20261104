import YM.Integration.WilsonReceivedCloseCalibratedSources
import YM.Integration.WilsonReceivedCloseOrdinaryPurchase

/-! The unweighted physical AB−C comparison for two genuinely appointed original Q rosters. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseCalibratedOrdinary
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
  (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
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

local notation "fixedFee" => 5*κ*(3:ℝ)^prec*(units)^2
local notation "singletonBank" => WilsonReceivedSingletonWindow.original R simple D φ protection mixGrades order shelf k op.count span height angleCap capPos

private theorem sold {y weightReal h sourceUnit allUnits : ℝ} (Y:1 ≤ y) (hn:1 ≤ h) (wp:0 ≤ weightReal) (Sn:0 ≤ sourceUnit)
    (au:1 ≤ allUnits) (inc:sourceUnit ≤ allUnits) {p D expo : ℕ} (de:p ≤ D) (ed:expo ≤ 2)
    (purchase:1 ≤ h^expo*(sourceUnit*y^(2*p))*weightReal) : 1 ≤ h^2*(allUnits*y^(2*D))*weightReal := by
  apply purchase.trans
  apply mul_le_mul_of_nonneg_right _ wp
  exact mul_le_mul (pow_le_pow_right₀ hn ed) (mul_le_mul inc
    (pow_le_pow_right₀ Y (Nat.mul_le_mul_left 2 de)) (pow_nonneg (zero_le_one.trans Y) _)
    (zero_le_one.trans au)) (mul_nonneg Sn (pow_nonneg (zero_le_one.trans Y) _)) (sq_nonneg _)

include course path cut simple sep in
theorem original (scroll:VowsR.LawScroll G φ)
    (chamber:VowsR.Chamber scroll R.kit D Q books) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (upperCount:op.count=Fintype.card V) (upperStage:op.stage=order+1)
    (heldShelf:shelf=reserve) (fundedGrade:k=order+shelf+Fintype.card V)
    (qualified:(eventually_atTop.mp upperBank).choose ≤ j+1) (within:∀a,upperOrders a ≤ upperOrder)
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
    (degree q : ℕ) {cap δ : ℝ} (cn : 0 ≤ cap) (dp : 0 < δ)
    (ready : WilsonReceivedCloseSignedPrice.opening R simple degree 2 prec op.count cn («η»:=1) zero_lt_one kp.le ≤ j)
    (clock : (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose ≤ j)
    (runRate : (eventually_atTop.mp (WilsonReceivedCloseCalibratedBudget.original R simple prec kp)).choose ≤ j)
    (birthCalendar : (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ j)
    (cool : (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ j)
    (endBills : (eventually_atTop.mp (WilsonReceivedCloseEndpoint.original R simple (2*2) («η»:=1) zero_lt_one)).choose ≤ j)
    (swept : (eventually_atTop.mp (WilsonReceivedCloseEndpoint.with_history R simple degree (2*2) 0
      cn («η»:=1) zero_lt_one (le_rfl : 0 ≤ (0:ℝ)))).choose ≤ j)
    (massDate : (eventually_atTop.mp singletonBank).choose ≤ m)
    (paidFee : (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
      (WilsonReceivedCloseOrdinaryPurchase.nonneg (cash:=fixedFee) (unit:=units)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) kp.le) (pow_nonneg (by norm_num) _)) (sq_nonneg _))
        (zero_le_one.trans (le_max_left _ _)) q sourceOrder) dp)).choose ≤ j)
    (reserveOrder : q+6*sourceOrder+5 ≤ prec) (close : PaceR.Close R degree cap m j) :
    ∃ (voter : ballot) (initial : P₀),
      initial.modelIndex=(namesOf voter) ∧
      (∀ y, Air.craft initial.model (fun d=>(initial.model d).paint y) mixGrades (π (j+1)) T₀ =
        Air.craft (merged voter) (fun d=>((merged voter) d).paint y) mixGrades (π (j+1)) T₀) ∧
      ∀ (a second c : V) (s : (Stock.census V).Mode), a ≠ second → s.val = {a,second} →
        ({a,second,c}:Finset V) ⊆ old ∪ fresh →
        WilsonReceivedCloseOrdinaryPurchase.Heard R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf op.count
          floor physical initial nextCut span height angleCap c s (δ*(g j)^q) := by
  have offered := WilsonReceivedCloseCalibratedSources.original
      (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ) (u:=u) (μ:=μ) (extra:=extra) («free»:=free)
      (D:=D) (income:=income) (K:=K) («freePos»:=freePos) (hk:=hk) (Q:=Q) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (course:=course)
      (path:=path) (books:=books) (floor:=floor) (cut:=cut) (op:=op) (lesson:=lesson) (ahead:=ahead)
      (way:=way) (ticket:=ticket) (warm:=warm) (education:=education) (employment:=employment)
      (calendar:=calendar) (hospital:=hospital) (pass:=pass) (upperJ:=upperJ) (upperQ:=upperQ)
      (upperLabels:=upperLabels) (upperClock:=upperClock) (upperExtra:=upperExtra) («upperFree»:=upperFree)
      («upperPos»:=upperPos) (upperOrder:=upperOrder) (target:=target) (order:=order) (shelf:=shelf)
      (upperRank:=upperRank) (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites)
      (orders:=orders) (old:=old) (fresh:=fresh) (sep:=sep) 
      (prec:=prec) (span:=span) (protection:=protection) (deep:=deep) (aged:=aged)
      (height:=height) (angleCap:=angleCap) (capPos:=capPos) (kp:=kp) scroll chamber month upperCount upperStage heldShelf fundedGrade qualified within top load narrow fits
      packed late funded ordersOK rank count level x fund thin unit stage openRead lateStamp
      degree 2 cn (by norm_num : (0:ℝ)<1) ready clock runRate birthCalendar cool endBills (by omega) close
  obtain ⟨voter,initial,index,air,oldSold,freshSold,slate⟩ := offered
  refine ⟨voter,initial,index,air,?_⟩
  intro a second c s diff pair named
  have zero : 0 ≤ units := zero_le_one.trans (le_max_left _ _)
  have feeZero : 0 ≤ fixedFee :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) kp.le) (pow_nonneg (by norm_num) _)) (sq_nonneg _)
  have h₁ : 1 ≤ restore :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (budget_pos R)) (one_le_pow₀ (budget_pos R))
  have temps := (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose_spec
    j cool N per (nextCut).le
  have small : g j ≤ 1 := by linarith only [temps.1,temps.2]
  have inv₁ : 1 ≤ (g j)⁻¹ := by rw [←one_div,le_div_iff₀ temps.1,one_mul]; exact small
  let deployed := groupToll initial
  have wp (v:V) : 0 < deployed v := by
    dsimp only [deployed,WilsonReceivedCloseRadiusAccount.registered]
    split_ifs <;> first | exact zero_lt_one | exact initial.salary.positive v
  have unitAt (v:V) (seen:v∈({a,second,c}:Finset V)) : deployed v=1 := by
    dsimp only [deployed,WilsonReceivedCloseRadiusAccount.registered]
    rcases Finset.mem_union.mp (named seen) with ho|hf
    · simp [ho]
    · simp [hf]
  have funds (v:V) (seen:v∈({a,second,c}:Finset V)) :
      1 ≤ restore^2*((units)*((g j)⁻¹)^(2*sourceOrder))*initial.w v := by
    rcases Finset.mem_union.mp (named seen) with ho|hf
    · have Cpos : 0 ≤ (Classical.choose purchased) := zero_le_one.trans (Classical.choose_spec purchased).1
      apply sold inv₁ h₁ (initial.salary.positive v).le
        (mul_nonneg (mul_nonneg (by norm_num) Cpos) (pow_nonneg (by norm_num) _)) (le_max_left _ _)
        ((le_max_left _ _).trans (le_max_right _ _)) (le_max_left _ _) (le_rfl:2 ≤ 2)
      exact oldSold v ho
    · have sourcePos : 0 ≤ factor := zero_le_one.trans (Classical.choose_spec offer).1
      have stepPos : 0 ≤ max (2*factor) (Classical.choose incomeQ) :=
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) sourcePos).trans (le_max_left _ _)
      apply sold inv₁ h₁ (initial.salary.positive v).le (mul_nonneg stepPos (pow_nonneg (by norm_num) _))
        (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _)) (le_max_right _ _) (by decide:1 ≤ 2)
      simpa only [pow_one] using freshSold v hf
  exact WilsonReceivedCloseOrdinaryPurchase.original R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf
    op.count floor physical initial nextCut simple course stage protection scroll chamber fund a second c s diff pair
    q prec sourceOrder span degree (fixedFee) (units) δ height angleCap cap feeZero zero dp capPos cn reserveOrder
    (by omega) deployed wp unitAt funds slate close swept clock birthCalendar cool massDate paidFee

end YM.Integration.WilsonReceivedCloseCalibratedOrdinary
