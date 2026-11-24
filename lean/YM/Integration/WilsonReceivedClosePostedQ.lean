import YM.Integration.WilsonReceivedCloseQCalendar
/-! The complete signed original two-date Q insertion on a named finite-period paid course.
Its common post precedes all tested fields and subsets. The cofinal gate precedes the two physical regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedClosePostedQ
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

local notation "faceFee" n:max => 5*κ*(3:ℝ)^prec*(units)^n
local notation "connectedOrder" a:max q:max => q+(2*sourceOrder+1)*a+1+a
local notation "allMass" => WilsonReceivedLogWindow.original R simple D φ protection mixGrades order shelf k op.count span height angleCap capPos

local notation "QTable" arity:max q:max δ:max =>
    ∃ (voter : ballot) (initial : P₀),
      initial.modelIndex=(namesOf voter) ∧
      (∀ y, Air.craft initial.model (fun d=>(initial.model d).paint y) mixGrades (π (j+1)) T₀ =
        Air.craft (merged voter) (fun d=>((merged voter) d).paint y) mixGrades (π (j+1)) T₀) ∧
      WilsonReceivedCloseNamedWallet.Sold R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf op.count
        floor physical initial (old ∪ fresh) ((units)*((g j)⁻¹)^(2*sourceOrder+1)) ∧
      WilsonReceivedCloseOrdinaryRoster.Served R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf op.count
        floor physical initial nextCut span height angleCap (old ∪ fresh) arity
          ((units)*((g j)⁻¹)^(2*sourceOrder+1)) ((g j)^(connectedOrder arity q)) (δ*(g j)^q)
def Receipt (arity comparison:ℕ) (ε:ℝ) : Prop := QTable arity comparison ε

include course path cut simple sep in
theorem issued (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (counter:op.count=Fintype.card V) (stage:op.stage=order+1)
    (filing:shelf=reserve) (size:k=order+shelf+Fintype.card V)
    (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (narrow:shelf ≤ R.alloy.B.a.clock.J m) (room:k ≤ R.alloy.B.a.clock.J m)
    (upperOrdersOK:∀v,upperOrders v≤upperOrder) (ordersOK:∀v,orders v≤K)
    (lowerRank:ActualOriginalQLayout.rankCap R u≤order) (mass:gradeTotal old grades tQ ≤ shelf)
    (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay) (unit:κ≤1)
    (shape arity comparison:ℕ) {cap ε:ℝ} (cn:0≤cap) (ep:0<ε)
    (reserves:2*sourceOrder*arity+(connectedOrder arity comparison)+3≤prec)
    (dates:WilsonReceivedCloseQCalendar.Window R simple request freshQ u μ extra D income K
      (k:=k) Q books ahead way ticket warm education employment calendar hospital pass upperJ upperQ upperLabels
      upperClock upperExtra upperOrder target order shelf upperRank old protection prec span deep aged height
      angleCap capPos kp shape arity comparison cn ep m j)
    (close:PaceR.Close R shape cap m j) : QTable arity comparison ε := by
  have a:op.count≤Burn.horizon k+2 := by unfold Burn.horizon; omega
  have o:order≤Burn.horizon k+1 := by unfold Burn.horizon; omega
  have c:order+shelf≤Burn.horizon k+2 := by unfold Burn.horizon; omega
  have floor' := narrow.trans ((A).fits.mono floor)
  let x:Wallet A₂ := WilsonMixedTestTableau.pair actors freshA (fun v=>⟨0,WilsonOriginalMixedTestTableau.zero upperDatum v⟩)
    (fun v=>⟨0,WilsonOriginalMixedTestTableau.zero datum v⟩)
  let startMass (slots:ℕ) := (eventually_atTop.mp (WilsonReceivedLogWindow.original
    R simple D φ protection mixGrades order shelf k slots span height angleCap capPos)).choose
  have paidMass : startMass (Fintype.card V) ≤ m := dates.mass
  have massGate : startMass op.count ≤ m := counter.symm ▸ paidMass
  exact WilsonReceivedCloseCalibratedMoments.original (R:=R) (simple:=simple)
    (request:=request) (freshQ:=freshQ) (u:=u) (μ:=μ) (extra:=extra) (D:=D) (income:=income) (K:=K)
    (hk:=hk) (Q:=Q) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (course:=course) (path:=path) (books:=books)
    (floor:=floor) (cut:=cut) (op:=op) (lesson:=lesson) (ahead:=ahead) (way:=way) (ticket:=ticket)
    (warm:=warm) (education:=education) (employment:=employment) (calendar:=calendar) (hospital:=hospital)
    (pass:=pass) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
    (upperExtra:=upperExtra) (upperOrder:=upperOrder) (target:=target) (order:=order) (shelf:=shelf)
    (upperRank:=upperRank) (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders)
    (old:=old) (fresh:=fresh) (sep:=sep) (protection:=protection) (prec:=prec) (span:=span)
    (deep:=deep) (aged:=aged) (height:=height) (angleCap:=angleCap) (capPos:=capPos) (kp:=kp)
    scroll chamber month counter stage filing size dates.upper upperOrdersOK top a floor' o c
    dates.fresh dates.birth ordersOK lowerRank counter.ge mass x fund narrow unit room (by simpa only [counter] using dates.reading)
    dates.stamp shape arity comparison cn ep (by simpa only [counter] using dates.signed) dates.clock dates.rent dates.nextHat
    dates.cool dates.endpoints dates.swept massGate dates.faceCharge dates.ordinary reserves close

end YM.Integration.WilsonReceivedClosePostedQ
