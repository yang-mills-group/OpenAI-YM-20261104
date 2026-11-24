import YM.Integration.WilsonReceivedTwoDateSigned
import YM.Integration.WilsonReceivedCalibratedAppointment
import YM.Integration.WilsonReceivedCalibratedTest

/-! The signed two-date price for an original paid curvature appointment and a new
registered curvature source, on the one reclosed Wilson density. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedFirstCalibratedQ
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
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (simple : G.Simple) {B : MS.Local.Physical.Deck G}
  {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] (request : Request V) (freshQ : MS.Land.Prescription B)
  (u : V → MS.Rake.Label B) (μ : ℝ) (extra : V → ℕ) (free : V → ℝ)
  {φ : ℕ → ℕ} (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
  (K q : ℕ) (freePos : ∀ v, 0 < free v) {ε : ℝ} (allow : 0 < ε)
local notation "offer" => WilsonOriginalMixedFiniteVoter.original R request freshQ u μ extra free D income simple K q freePos allow
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
local notation "purchased" => WilsonReceivedCalibratedUpper.original R simple upperJ upperQ upperLabels upperClock
  upperExtra upperFree D Q way ticket warm income books ahead education employment calendar hospital pass
  upperOrder order q target upperRank upperPos allow
local notation "upperBank" => (Classical.choose_spec purchased).2.choose_spec
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
local notation "birth" => fun x U=>Poly.pass (MergeProof.Accent.Mach (Stock.census V) (fun v =>
  ActualRunQlocalNativeTuple.reader datum v (testInclusion (ActualRunQlocalNativeTuple.orbit datum) (rTest x) v) *
    ActualOriginalCalibratedColumns.weightedObservable R B freshQ (u v) η (R.family.side i₁ per)
      (ActualRunQlocalNativeTuple.root datum v) U (orders v)))
local notation "physical" => fun x U=>birth x U * prior x U
local notation "move" => (R.family.path.levels.clock.op j per)
open QuadraticLocal.Affinity VowsR QuadraticLocal.Mentor


variable (mask : (Stock.census V).Mode) (root : V) (onMask : root ∈ mask.val)
  (prec span slots : ℕ) (precise : 2*(prec+1)+8 ≤ order) (journal : prec+4 ≤ 3*k+2)
  (gain cap : ℝ) (cap₀ : 0 ≤ cap) {κ : ℝ} (κ₀ : 0 < κ)
  (widths : ∀ s n : ℕ, n ≤ s → ∀ β : ℝ, R.alloy.delay.betaEntry s ≤ β →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon n) s)⁻¹^2) ≤ β)
local notation "receiver" => WilsonReceivedPaidCourse.original R simple D φ widths mixGrades mask root onMask
  prec span order shelf k slots precise journal gain cap cap₀ κ₀
local notation "fineG" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
local notation "lowerG" => Coat.gStep (R.family.path.rep N per (j+1)).beta

include course path cut simple sep in
theorem original (scroll:VowsR.LawScroll G φ)
    (chamber:VowsR.Chamber scroll R.kit D Q books) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (upperCount:op.count=Fintype.card V) (upperStage:op.stage=order+1)
    (heldShelf:shelf=reserve) (fundedGrade:k=order+shelf+Fintype.card V)
    (qualified:(eventually_atTop.mp upperBank).choose≤j+1) (within:∀a,upperOrders a≤upperOrder)
    (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (load:op.count ≤ depth) (narrow:shelf ≤ R.alloy.B.a.clock.J j) (fits:order ≤ Burn.horizon k+1)
    (packed:order+shelf ≤ depth) (late:WilsonOriginalMixedStampedFinite.firstDate R simple request freshQ u μ extra free D income K q freePos allow ≤ j)
    (funded:m₀ ≤ j+1) (Ω:ℝ) (one:1 ≤ Ω) (pageCap:Ω ≤ page) (ordersOK:∀v,orders v ≤ K)
    (rank:ActualOriginalQLayout.rankCap R u ≤ order) (count:Fintype.card V ≤ op.count)
    (level:gradeTotal old grades tQ ≤ shelf)
    (x : Wallet A₂) (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (fitStage : k ≤ R.alloy.B.a.clock.J j) (headcount : op.count=slots)
    (dominate : budgetR R j ≤ Ω)
    (lateRead : (eventually_atTop.mp receiver).choose ≤ j)
    (lateStamp : WilsonReceivedMeasuredStampPrice.opening R simple prec order k
      (by omega) (by omega) κ₀ ≤ j+1) :
    ∃ vote:ballot, ∃ (jointRadius : V → ℝ) (h : ℝ), 1 ≤ h ∧ h ≤ max (max 1 (bill)) (elected^5+1) ∧
      (∀ v ∈ old, jointRadius v=w v/(max 1 (Ω*(rebate*cost)))/2) ∧
      (∀ v ∈ fresh, jointRadius v=min (free v/(paidScale*Ω)/2)
        (free v/((Classical.choose incomeQ*xβ^((Classical.choose_spec incomeQ).2.choose+1))*risk))) ∧
      ∀ (F : Forest (move).ratio) (tag : (move).Choices) (A' : Stationary.Link G (R.family.side j per)),
      let angle := Stationary.arm G (R.family.side j per) 1 A'
      let B' := R.family.path.levels.budget j
      let β' := R.family.path.levels.clock.hatBeta j
      ∀ z : ℝ, |z| ≤ |gain| * (Real.log β')^span*((B'.B:ℝ)^2*B'.threshold)/lowerG →
        (∀ a, ‖Exterior.collect G angle a‖ ≤ cap*|z|) →
        let W := Integral.sample lowerG angle
        flags (Ψ j).p.threshold W=∅ →
        let heard := Order.logTo (Fintype.card V) ((((Ψ j).eval W:ℂ)⁻¹) •
          LocalComparison.actualPush R.family N per j (physical x) W)
        let deposited := Air.craft (oldRows vote) (fun a => ((oldRows vote) a).paint (l x)) grades (π (j+1)) T₀
        let Qtest := testInclusion (ActualRunQlocalNativeTuple.orbit datum) (rTest x)
        let planted := NativePaidPacketColors.colors (ActualOriginalQPackets.packets freshQ datum u η orders N) deposited.vac Qtest
        let filed := WilsonOriginalMixedFiniteMaterial.bank old fresh deposited planted
        let step := (RunFormalChain.fromRun R).step N j per nextCut
        let wick := Order.value (lowerG:ℂ) (Order.logMarked (Bulk.Fk step F tag filed angle order))
        Poly.toll (QuadraticLocal.Stoop.radius jointRadius h) mask * ‖(heard-wick).part mask‖ ≤
          8*(budgetR R j)^slots*(8*elected*e+κ*fineG^prec)+κ*lowerG^prec := by
  obtain ⟨vote,input,read,notes,taut,crown,clear,_,forced⟩:=
    WilsonReceivedCalibratedAppointment.original (R:=R) (simple:=simple) (D:=D) (income:=income) (q:=q) (allow:=allow)
      (hk:=hk) (Q:=Q) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (course:=course) (books:=books) (floor:=floor) (cut:=cut) (op:=op)
      (lesson:=lesson) (ahead:=ahead) (way:=way) (ticket:=ticket) (warm:=warm) (education:=education)
      (employment:=employment) (calendar:=calendar) (hospital:=hospital) (pass:=pass) (upperJ:=upperJ)
      (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock) (upperExtra:=upperExtra) (upperFree:=upperFree)
      (upperPos:=upperPos) (upperOrder:=upperOrder) (target:=target) (order:=order) (shelf:=shelf)
      (upperRank:=upperRank) (upperSites:=upperSites) (upperOrders:=upperOrders)
      upperCount upperStage heldShelf fundedGrade qualified within top
  have rootPos:(1:ℝ) ≤ (A).clock.hatBeta ((j+1)+1):=((A).fits.delayed ((j+1)+1)).le
  have active:0<e:=Real.rpow_pos_of_pos (zero_lt_one.trans_le rootPos) _
  have regularCap:e≤1:=Real.rpow_le_one_of_one_le_of_nonpos rootPos (neg_nonpos.mpr (Nat.cast_nonneg _))
  have early:=input.old.loan_monotone (clear (Ψ ((j+1)+1)).p.supportExponent (Ψ ((j+1)+1)).p.B) active.le
  have school:=WilsonOriginalProjectedCurvatureTableau.real upperDatum upperQ upperLabels upperFee upperOrders N agenda upperExtra
  obtain ⟨jointRadius,h,oneH,hCap,oldCost,newCost,estimate⟩:=
    WilsonReceivedTwoDateSigned.original R simple request freshQ u μ extra free D income K q freePos allow
      hk Q π Γ Ψ course path books floor cut op lesson ahead actors M w grades order shelf vote
      sites orders pieces₀ old fresh sep zeroA warm input mask root onMask prec span slots precise journal
      gain cap cap₀ κ₀ widths pass scroll chamber month hospital load narrow fits packed late
      funded Ω one pageCap ordersOK rank count level active regularCap (le_refl _) notes school early
      forced taut crown x fund fitStage headcount dominate lateRead lateStamp
  refine ⟨vote,jointRadius,h,oneH,hCap,oldCost,newCost,?_⟩
  intro F tag θ α B' β' z zmax αmax W healthy heard deposited Qtest planted filed step wick
  have same : (sheet).push (Ψ ((j+1)+1)).beta ((QuadraticLocal.Tint.Patrol.picture M input).density (l x)) =
      prior x := congrArg ((sheet).push (Ψ ((j+1)+1)).beta) (funext (read (l x)))
  let amount (f:Config G (R.family.side (j+1) per)→Poly (Stock.census V)) : ℝ :=
    Poly.toll (QuadraticLocal.Stoop.radius jointRadius h) mask *
      ‖(Order.logTo (Fintype.card V) (((Ψ j).eval W:ℂ)⁻¹ • LocalComparison.actualPush R.family N per j
        (fun U=>birth x U*f U) W)-wick).part mask‖
  exact (congrArg amount same).symm.le.trans (estimate F tag θ z zmax αmax healthy)

end YM.Integration.WilsonReceivedFirstCalibratedQ
