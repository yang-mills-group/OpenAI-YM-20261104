import YM.Integration.WilsonOriginalTwoDateQHistory
import YM.Integration.WilsonReceivedMeasuredStampPrice
import YM.Integration.WilsonReceivedPaidCourse

/-! The physically deposited and newly planted fields, heard together on the
second measured block against the independent finite periodic programme. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedTwoDateSigned
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
  {V : Type} [DecidableEq V] [Fintype V] (request : Request V) (freshQ : MS.Land.Prescription B)
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
  {ι : Type} {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  {P : Earn.Passport (R.family.side ((j+1)+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row P (Stock.census V) G (Affinity.Wallet actors))
  (w : V → ℝ) (grades : V → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J (j+1)))
local notation "M₁" => Oak.student (m:=m) (i:=j+1) (n:=per) (N:=N) (k:=k) R hk D Q π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead actors M order voter
local notation "ζ" => Oak.grade0 R hk D Q π Γ (floor.trans (Nat.le_succ j)) lesson
local notation "oldRows" => Mutation.stamp M₁ (Γ (j+1)) ζ depth order
local notation "file" => litP D R.alloy Q (hk.trans (R.alloy.B.a.fits.mono (floor.trans (Nat.le_succ j)))) lesson.entry
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "fig" => Oak.figureReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead order shelf
local notation "rebate" => Oak.rebate R hk D Q π Γ (floor.trans (Nat.le_succ j)) op lesson
local notation "page" => WilsonMovingMentorPageRefund.cap R j
local notation "tQ" => (fun _ : V => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u)
variable (sites : V → Site (R.family.side (j+1) per)) (orders : V → ℕ)
local notation "datum" => ActualOriginalQPointSetup.pointDatum R request per (j+1) sites
local notation "η" => (μ+R.family.S.scale N-R.family.S.scale (j+1))-R.family.S.scale N
local notation "newRows" => WilsonOriginalProjectedCurvatureLamps.cohort freshQ datum u η orders N σ extra

variable (pieces₀:∀ v,Submodule ℝ (X v)) (old fresh:Finset V) (sep:Disjoint old fresh) (zeroA:∀v,0∈actors v)
  (warm:QuadraticLocal.Spill.Raffle.Warm G D R.alloy.delay φ)
local notation "freshA" => WilsonOriginalProjectedCurvatureTableau.actors datum
local notation "Knew" => (fun v=>(WilsonOriginalProjectedCurvatureTableau.nulls datum v).restrictScalars ℝ)
local notation "A₂" => WilsonMixedTestTableau.actors actors freshA
local notation "l" => WilsonMixedTestTableau.left actors freshA old zeroA
local notation "rTest" => WilsonMixedTestTableau.right actors freshA fresh (WilsonOriginalMixedTestTableau.zero datum)
local notation "mixed" => WilsonMixedFaceLog.routed oldRows newRows old fresh sep l rTest
local notation "mixGrades" => choice old grades tQ
local notation "sheet" => Pane.panel R.alloy (j+1) (R.alloy.B.a.S.oneStep (j+1) per).exact_size
local notation "home" => P.coarser (sheet).ratio
local notation "xβ" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "paidScale" => factor*xβ^(exponent+1)
local notation "hQ" => ActualOriginalQLayout.rankCap R u+Fintype.card V*WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u+1
local notation "risk" => (xβ^QuadraticLocal.Spill.Raffle.pad hQ)
local notation "incomeQ" => WilsonOriginalFreshQAtReceivedDate.prepaid R simple request freshQ u μ extra free D income warm K freePos
local notation "entrance" => (Classical.choose_spec incomeQ).2.choose_spec
local notation "m₀" => WilsonOriginalJointQWallet.firstBirth R simple request freshQ u μ extra free D income K freePos warm
local notation "hβ" => R.alloy.B.a.clock.J (j+1)


variable [Countable ι] {c₀:Type} [Countable c₀]
  (before:QuadraticLocal.Tint.Incoming P (Ψ ((j+1)+1)) (Affinity.Wallet actors) c₀ (Stock.census V))
  {b e:ℝ}
local notation "A" => R.alloy.B.a
local notation "i₁" => (j+1)
local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "nextCut" => (Nat.lt_trans (Nat.lt_succ_self j) cut)
local notation "H" => Ψ (j+1)
local notation "w₀" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "vac" => Burn.young ((A).clock.hatBeta ((j+1)+1)) k
local notation "elected" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "ratio" => (sheet).ratio
local notation "cost" => (fig).produce (ratio).count*b
local notation "spent" => (fig).hitPrice G (ratio).count (Ψ ((j+1)+1)).p (H).p b e vac w₀
local notation "fee" => QuadraticLocal.Earn.Invoice.price (H).p (fig).mist (order+shelf+1) op.count ((H).p.supportExponent+1+1) (fig).limitC G
local notation "bill" => (fig).fidelity*fee*(cost)+spent
local notation "joint" => WilsonMixedPassportRows.passport (WilsonMixedPassportRows.owner home (paper datum u) old)
local notation "K₂" => WilsonMixedTestTableau.pieces pieces₀ Knew
local notation "prior" => fun x=> (sheet).push (Ψ ((j+1)+1)).beta ((QuadraticLocal.Tint.Patrol.picture M before).density (l x))
local notation "physical" => fun x U=>Poly.pass (MergeProof.Accent.Mach (Stock.census V) (fun v =>
  ActualRunQlocalNativeTuple.reader datum v (testInclusion (ActualRunQlocalNativeTuple.orbit datum) (rTest x) v) *
    ActualOriginalCalibratedColumns.weightedObservable R B freshQ (u v) η (R.family.side i₁ per)
      (ActualRunQlocalNativeTuple.root datum v) U (orders v))) * (prior x U)
local notation "agenda" => QuadraticLocal.Poetry.Agenda.seed D φ (Burn.horizon k) ((A).clock.J ((j+1)+1))
local notation "wage" => ((H).p.supportExponent+1+1)
local notation "move" => (R.family.path.levels.clock.op j per)
local notation "rSupport" => ((joint).coarser (move).ratio)
local notation "spare" => QuadraticLocal.Willow.haloSlack ((A).budget (j+1)).B
local notation "df" => (LocalComparison.forcedDivisor R.family (j+1))
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

include course path cut simple voter sep in
theorem original (pass:Pass D Q R.alloy R.kit) (scroll:VowsR.LawScroll G φ)
    (chamber:VowsR.Chamber scroll R.kit D Q books) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (load:op.count ≤ depth) (narrow:shelf ≤ R.alloy.B.a.clock.J j) (fits:order ≤ Burn.horizon k+1)
    (packed:order+shelf ≤ depth) (late:WilsonOriginalMixedStampedFinite.firstDate R simple request freshQ u μ extra free D income K q freePos allow ≤ j)
    (funded:m₀ ≤ j+1) (Ω:ℝ) (one:1 ≤ Ω) (pageCap:Ω ≤ page) (ordersOK:∀v,orders v ≤ K)
    (rank:ActualOriginalQLayout.rankCap R u ≤ order) (count:Fintype.card V ≤ op.count)
    (level:gradeTotal old grades tQ ≤ shelf)
    (active:0<e) (regularCap:e ≤ 1) (firstFee:b ≤ elected⁻¹)
    (notes:Scene.Armada M w grades agenda b order op.count shelf) (school:Tableau pieces₀ actors M)
    (earlier:before.old.Paid w (Ψ ((j+1)+1)).p.B (Ψ ((j+1)+1)).p.supportExponent e)
    (forced:before.hard.Paid w (Ψ ((j+1)+1)).p.B (Ψ ((j+1)+1)).p.supportExponent 1)
    (oldModes:Taut P.support actors pieces₀ before.old) (hardModes:Crown P.support actors pieces₀ before.hard)
    (x : Wallet A₂) (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (fitStage : k ≤ R.alloy.B.a.clock.J j) (headcount : op.count=slots)
    (dominate : budgetR R j ≤ Ω)
    (lateRead : (eventually_atTop.mp receiver).choose ≤ j)
    (lateStamp : WilsonReceivedMeasuredStampPrice.opening R simple prec order k
      (by omega) (by omega) κ₀ ≤ j+1) :
    ∃ (jointRadius : V → ℝ) (h : ℝ), 1 ≤ h ∧ h ≤ max (max 1 (bill)) (elected^5+1) ∧
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
        let deposited := Air.craft oldRows (fun a => (oldRows a).paint (l x)) grades (π (j+1)) T₀
        let Qtest := testInclusion (ActualRunQlocalNativeTuple.orbit datum) (rTest x)
        let planted := NativePaidPacketColors.colors (ActualOriginalQPackets.packets freshQ datum u η orders N) deposited.vac Qtest
        let filed := WilsonOriginalMixedFiniteMaterial.bank old fresh deposited planted
        let step := (RunFormalChain.fromRun R).step N j per nextCut
        let wick := Order.value (lowerG:ℂ) (Order.logMarked (Bulk.Fk step F tag filed angle order))
        Poly.toll (QuadraticLocal.Stoop.radius jointRadius h) mask * ‖(heard-wick).part mask‖ ≤
          8*(budgetR R j)^slots*(8*elected*e+κ*fineG^prec)+κ*lowerG^prec := by
  have oldCharge := WilsonReceivedMeasuredStampPrice.original R hk D Q π Γ Ψ course books hi cut op lesson ahead
    actors M order shelf voter pass hospital (narrow.trans ((A).fits.mono (Nat.le_succ j))) load simple prec
    (by omega) (by omega) κ₀ lateStamp (Push.AbsoluteSums.budget_nonneg (notes.suggests 0)) firstFee active.le
  obtain ⟨jointRadius,h,restore,h₁,hMax,oldWallet,newWallet,capRestore,rosterCount,issue⟩ :=
    WilsonOriginalTwoDateQHistory.original R simple request freshQ u μ extra free D income K q freePos allow
      hk Q π Γ Ψ course path books floor cut op lesson ahead actors M w grades order shelf voter
      sites orders pieces₀ old fresh sep zeroA warm before pass scroll chamber month hospital load narrow fits
      packed late funded Ω one pageCap ordersOK rank count level active regularCap firstFee notes school earlier
      forced oldModes hardModes x
  refine ⟨jointRadius,h,h₁,hMax,oldWallet,newWallet,?_⟩
  let plan : Syl.School k := ⟨order,op.count,shelf,load,fits,packed⟩
  let nextOp := plan.room (step_paid (A) j) (hk.trans ((A).fits.mono floor))
  letI := rosterCount
  intro F tag A' angle B' β' z extensive angles W healthy heard deposited Qtest planted filed step wick
  let arranged := Air.craft mixed (fun a => (mixed a).paint x) mixGrades (π (j+1)) T₀
  have higher : shelf≤(A).clock.J (j+1) := narrow.trans ((A).fits.mono (Nat.le_succ j))
  have rich : 1 ≤ elected := (by norm_num : (1:ℝ)≤4).trans (MintClock.Page.roofers ..)
  obtain ⟨cal⟩ := Oak.agrees R hk D Q π Γ Ψ course hi cut lesson
  obtain ⟨c₁,_,upperOut,upperStory⟩ :=
    Oak.Buffered.arrive R simple hk D Q π Γ Ψ course scroll books chamber hi cut op lesson cal ahead hospital
      actors pieces₀ M before w grades order shelf voter e b load higher notes school (l x)
      oldModes hardModes earlier forced (firstFee.trans (inv_le_one_of_one_le₀ rich)) active regularCap
  have formal := WilsonOriginalSignedDatedFinite.measured R simple request freshQ u μ extra free D income K q freePos allow
    hk Q π Γ Ψ course path books floor cut op lesson ahead actors M w grades order shelf voter sites orders old fresh sep
    l rTest x pass month (cost) upperStory.earning load higher fits packed late Ω one pageCap ordersOK rank count level F tag angle order
  have bankSame : Bulk.Fk step F tag arranged angle order = Bulk.Fk step F tag filed angle order := formal.2.2.2.2.1
  let Kout := 8*(budgetR R j)^slots
  let oldBound := 8*elected*e+κ*fineG^prec
  have fundedUpper : 0 ≤ elected := (by norm_num : (0:ℝ)≤4).trans (MintClock.Page.roofers ..)
  have money₀ : 0 ≤ oldBound := by
    dsimp only [oldBound]
    have hg : 0 ≤ fineG := by unfold Coat.gStep; positivity
    positivity
  have hpos : 0 < h := zero_lt_one.trans_le h₁
  have restamped : h⁻¹*(bill) ≤ oldBound := calc
    _ ≤ h⁻¹*oldBound := mul_le_mul_of_nonneg_left oldCharge (inv_nonneg.mpr hpos.le)
    _ ≤ oldBound := mul_le_of_le_one_left money₀ (inv_le_one_of_one_le₀ h₁)
  have readAt := (eventually_atTop.mp receiver).choose_spec j lateRead hk fitStage Q π Γ Ψ course books
    scroll chamber fund floor nextCut
  have price (τ : ℝ) (τpos : 0<τ) (τone : τ≤1) :
      Poly.toll (QuadraticLocal.Stoop.radius jointRadius h) mask*‖(heard-wick).part mask‖ ≤ Kout*(oldBound+τ)+κ*lowerG^prec := by
    obtain ⟨lesson₂,vote,c,d,hc,hd,input,output,story,salary,_,_,_,_,_,actual,_,_⟩ := issue τ τpos τone
    letI := hc
    letI := hd
    let nextExpense := Oak.expenseReal R hk D Q π Γ books floor nextOp lesson₂ ahead order shelf
    have posBuy : 0 < nextExpense := (by norm_num : (0:ℝ)<4).trans_le story.Waffle.strong
    have Ωpos : 0<Ω := zero_lt_one.trans_le one
    have fundedEntry : restore ≤ nextExpense⁻¹ := capRestore.trans <| calc
      h⁻¹*Ω⁻¹ ≤ Ω⁻¹ := mul_le_of_le_one_left (inv_nonneg.mpr Ωpos.le) (inv_le_one_of_one_le₀ h₁)
      _ ≤ nextExpense⁻¹ := inv_anti₀ posBuy (story.Beamwork.trans dominate)
    have tested := readAt nextOp headcount
      lesson₂ ahead A₂ mixed (QuadraticLocal.Stoop.radius jointRadius h) vote restore salary
      x F tag A' K₂ input (max (h⁻¹*(bill)) τ) output story fundedEntry z extensive angles healthy
    let called := Order.logTo (Fintype.card V) ((((Ψ j).eval W:ℂ)⁻¹) •
      LocalComparison.actualPush R.family N per j ((QuadraticLocal.Tint.Patrol.picture mixed input).density x) W)
    change Poly.toll (QuadraticLocal.Stoop.radius jointRadius h) mask*‖(called-Order.value (lowerG:ℂ)
      (Order.logMarked (Bulk.Fk step F tag arranged angle order))).part mask‖ ≤
      (8*nextExpense^nextOp.count)*max (h⁻¹*(bill)) τ+κ*lowerG^prec at tested
    rw [bankSame] at tested
    change Poly.toll (QuadraticLocal.Stoop.radius jointRadius h) mask*‖(called-wick).part mask‖ ≤ _ at tested
    have eqHeard : called = heard := by
      unfold called heard
      rw [show (QuadraticLocal.Tint.Patrol.picture mixed input).density x = physical x from funext (actual x)]
    rw [eqHeard] at tested
    have bound : max (h⁻¹*(bill)) τ ≤ oldBound+τ :=
      max_le (restamped.trans (le_add_of_nonneg_right τpos.le)) (le_add_of_nonneg_left money₀)
    have upperPrice : 8*nextExpense^nextOp.count ≤ Kout := by
      change 8*nextExpense^op.count ≤ 8*(budgetR R j)^slots
      rw [headcount]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ posBuy.le story.Beamwork _) (by norm_num)
    exact tested.trans (add_le_add (mul_le_mul upperPrice bound (τpos.le.trans (le_max_right _ _))
      (le_trans (by positivity : 0≤8*nextExpense^nextOp.count) upperPrice)) le_rfl)
  have fixed : 0 ≤ Kout := by
    have bought := issue 1 zero_lt_one le_rfl
    rcases bought with ⟨lesson₂,vote,c,d,_,_,input,output,story,_⟩
    have allowance : 0 ≤ budgetR R j := (by norm_num : (0:ℝ)≤4).trans (story.Waffle.strong.trans story.Beamwork)
    dsimp only [Kout]
    positivity
  apply le_of_forall_pos_le_add
  intro surplus hp
  let τ := min 1 (surplus/(Kout+1))
  have den : 0<Kout+1 := by linarith only [fixed]
  have τpos : 0<τ := lt_min zero_lt_one (div_pos hp den)
  have debit : Kout*τ ≤ surplus := calc
    _ ≤ (Kout+1)*τ := mul_le_mul_of_nonneg_right (by linarith) τpos.le
    _ = τ*(Kout+1) := mul_comm _ _
    _ ≤ _ := (le_div_iff₀ den).mp (min_le_right ..)
  have result := price τ τpos (min_le_left ..)
  change _ ≤ Kout*oldBound+κ*lowerG^prec+surplus
  linarith only [result,debit]

end YM.Integration.WilsonReceivedTwoDateSigned
