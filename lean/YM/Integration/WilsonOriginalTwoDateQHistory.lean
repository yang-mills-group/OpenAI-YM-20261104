import YM.Integration.WilsonOriginalJointQWallet
import YM.Integration.WilsonOriginalFiledSuccessStory
import YM.Integration.WilsonOriginalSignedDatedFinite
import YM.Integration.WilsonOriginalFreshQAtReceivedDate
import YM.Integration.WilsonOriginalSignedQAdmission
import YM.Integration.WilsonOriginalMixedFiniteVoter
import YM.Integration.WilsonOriginalMixedStampedFinite
import YM.Integration.WilsonOriginalMeasuredStampCoefficients

/-! On two adjacent dates of the actual course, retain the complete measured old rescaling and the independent fresh source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoDateQHistory
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

include course path cut simple in
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
    (x:Wallet A₂) :
    let plan:Syl.School k:=⟨order,op.count,shelf,load,fits,packed⟩
    let nextOp:=plan.room (step_paid (A) j) (hk.trans ((A).fits.mono floor))
    ∃ (jointRadius:V → ℝ) (h restore:ℝ),
      1 ≤ h ∧ h ≤ max (max 1 (bill)) (elected^5+1) ∧
      (∀v ∈ old,jointRadius v=w v/(max 1 (Ω*(rebate*cost)))/2) ∧
      (∀v ∈ fresh,jointRadius v=min (free v/(paidScale*Ω)/2)
        (free v/((Classical.choose incomeQ*xβ^((Classical.choose_spec incomeQ).2.choose+1))*risk))) ∧
      restore ≤ h⁻¹*Ω⁻¹ ∧
      Countable (WilsonMixedPassportRows.Face oldRows old ⊕ WilsonMixedPassportRows.Face newRows fresh) ∧
      ∀ (τ:ℝ), 0<τ → τ ≤ 1 →
      ∃ (lesson₂:Lesson (N:=N) R hk D Q π Γ floor)
        (vote:Cruise.Voter mixed σ order nextOp.count nextOp.stage k ((A).clock.J j)),
        ∃ (c d:Type), Countable c ∧ Countable d ∧
          ∃ (input:QuadraticLocal.Tint.Incoming joint H (Wallet A₂) c (Stock.census V))
            (output:QuadraticLocal.Tint.Incoming rSupport (Ψ j) (Wallet A₂) d (Stock.census V)),
            let w₂:=QuadraticLocal.Stoop.radius jointRadius h
            let e₂:=max (h⁻¹*(bill)) τ
            let nextM:=Oak.student (n:=per) R hk D Q π Γ books floor nextOp lesson₂ ahead A₂ mixed order vote
            Oak.Buffered.SuccessStory R hk D Q π Γ Ψ books floor nextOp lesson₂ ahead A₂ K₂ mixed input w₂ mixGrades order shelf vote e₂ restore output ∧
            Scene.Armada mixed w₂ mixGrades σ restore order nextOp.count shelf ∧ Tableau K₂ A₂ mixed ∧
            Taut (joint).support A₂ K₂ input.old ∧ Crown (joint).support A₂ K₂ input.hard ∧
            input.old.Paid w₂ (H).p.B wage (h⁻¹*(bill)) ∧
            input.hard.Paid w₂ (H).p.B (H).p.supportExponent df ∧
            (∀ x U,(QuadraticLocal.Tint.Patrol.picture mixed input).density x U=physical x U) ∧
            (∀ x U,((QuadraticLocal.Tint.Patrol.picture mixed input).density x U).part (Stock.census V).quiet=((H).eval U:ℂ)) ∧
            ∀ x,LocalComparison.actualPush R.family N per j (physical x)=(QuadraticLocal.Tint.Patrol.report nextM output (Coat.gStep (H).beta)).density x := by
  intro plan nextOp
  have deep:shelf ≤ (A).clock.J (j+1):=narrow.trans ((A).fits.mono (Nat.le_succ j))
  let F:=Classical.choice (Tree.select (move).ratio (move).patch.odd_side)
  let tag:(move).Choices:=Classical.choice inferInstance
  obtain ⟨wQ,w1,z,gross,qPress,pQ,pos,oldFit,hGross,birth,funds,feeCap,oldWallet,freshWallet,wQeq⟩:=
    WilsonOriginalJointQWallet.original R simple request freshQ u μ extra free D income K q freePos allow hk Q π Γ Ψ course path books
      floor cut op lesson ahead actors M w grades order shelf voter sites orders pieces₀ old fresh sep zeroA warm pass month
      (cost) load deep fits packed late funded Ω one pageCap ordersOK rank count level notes.positive x F tag 0 0
  obtain ⟨cal⟩:=Oak.agrees R hk D Q π Γ Ψ course hi cut lesson
  have entered:=WilsonOriginalSignedQAdmission.received R hk D Q π Γ Ψ course books hi cut op lesson ahead actors M w grades order shelf voter
    freshQ datum u η orders extra pieces₀ old fresh sep zeroA w1 wQ mixGrades before simple chamber.education pass (chamber.ready scroll) month hospital fits deep load cal
    (l x) active regularCap firstFee notes school earlier forced oldModes hardModes birth pos pQ oldFit funds 1 zero_lt_one
  rcases entered with ⟨small,realCost,feeDiv,hardOK,_tight,upper,c,cc,input,accepted,known,received,kept,modes,compulsory,shown,quiet⟩
  letI:=cc
  obtain ⟨lesson₂⟩:=Oak.tale R hk D Q π Γ floor nextCut path
  obtain ⟨cal₂⟩:=Oak.agrees R hk D Q π Γ Ψ course floor nextCut lesson₂
  haveI students:Countable (Scene.Texts M (sheet).ratio (Cruise.publish D R.rolls Q R.alloy φ books op
    (Oak.era R hk D Q π Γ hi op lesson) (R.alloy.B.a.S.oneStep i₁ per).exact_size M order voter lesson.entry)):=Scene.crewC M (sheet).ratio
      (Cruise.publish D R.rolls Q R.alloy φ books op (Oak.era R hk D Q π Γ hi op lesson)
        (R.alloy.B.a.S.oneStep i₁ per).exact_size M order voter lesson.entry)
      (Cruise.funded D R.rolls Q R.alloy φ books op (Oak.era R hk D Q π Γ hi op lesson)
        (R.alloy.B.a.S.oneStep i₁ per).exact_size M order voter lesson.entry lesson.studied ahead)
  haveI filedCount:Countable (Mutation.Names M₁ order):=by
    exact @Mutation.instCountable _ _ _ _ _ _ _ _ M₁ order students
  haveI leftCount:Countable (WilsonMixedPassportRows.Face oldRows old):=by
    unfold WilsonMixedPassportRows.Face
    infer_instance
  haveI rightCount:Countable (WilsonMixedPassportRows.Face newRows fresh):=by
    unfold WilsonMixedPassportRows.Face
    infer_instance
  let sale:=books.salary ((A).clock.J ((j+1)+1)) ((A).clock.J (j+1)) op
  let slip:=QuadraticLocal.Shelter.Deck.crewCost (fig).helmet ((H).p.supportExponent+1) (fig).bearing*
    ((sale.enroll xβ)^op.count*(sale.price xβ)+(fig).grow G (ratio).count (H).p b+(fig).pay (ratio).count (H).p b)
  let h₁:=WilsonRootedKioskFreeRadius.radius (max (bill/1) qPress) slip gross spare
  let w₂:=QuadraticLocal.Stoop.radius w1 h₁
  have unit:1 ≤ h₁:=(le_max_left 1 _).trans (le_max_left _ _)
  have ratioCap:gross/spare ≤ 1:=by
    apply (div_le_one (Willow.spare_pos _)).mpr
    simpa only [(course.1.walk i₁ hi cut.le).truep.point] using hGross
  have ticket:h₁ ≤ max (max 1 (bill)) (elected^5+1):=upper.trans (max_le_max
    (max_le (le_max_left _ _) (max_le (by simpa only [div_one] using (le_max_right 1 (bill))) (feeCap.trans ((inv_le_one_of_one_le₀ one).trans (le_max_left _ _))))) (add_le_add_right ratioCap _))
  refine ⟨w1,h₁,h₁⁻¹*qPress,unit,ticket,oldWallet,?_,mul_le_mul_of_nonneg_left feeCap (inv_nonneg.mpr (zero_le_one.trans unit)),inferInstance,?_⟩
  · intro v hv
    simpa only [wQeq v] using freshWallet v hv
  intro τ τpos τcap
  let e₂:=max (h₁⁻¹*(bill)) τ
  have posE:0<e₂:=τpos.trans_le (le_max_right _ _)
  have capE:e₂ ≤ 1:=max_le realCost τcap
  have native:input.old.Paid w₂ (H).p.B (H).p.supportExponent e₂:=by
    apply input.old.loan_monotone _ (le_max_left _ _)
    obtain ⟨f,hn,terms,sums⟩:=received.budget
    refine ⟨f,hn,terms,fun v=>Push.AbsoluteSums.budget_mono (sums v) ?_ ?_⟩
    · intro a
      split
      · exact mul_nonneg (mul_nonneg (Poly.worth accepted.positive _).le (hn a)) (Real.exp_nonneg _)
      · exact le_rfl
    · intro a
      split
      · apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (mul_nonneg (Poly.worth accepted.positive _).le (hn a))
        exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      · exact le_rfl
  have vote:=plan.future (step_paid (A) j) (hk.trans ((A).fits.mono floor)) mixGrades mixed accepted
  obtain ⟨d,cd,out,story⟩:=Oak.Buffered.arrive R simple hk D Q π Γ Ψ course scroll books chamber floor nextCut nextOp lesson₂ cal₂ ahead hospital
    A₂ K₂ mixed input w₂ mixGrades order shelf vote e₂ (h₁⁻¹*qPress) load narrow accepted known x modes compulsory native
    (Hard.mono _ kept hardOK) small posE capE
  refine ⟨lesson₂,vote,c,d,cc,cd,input,out,story,accepted,known,modes,compulsory,received,Hard.mono _ kept feeDiv,shown,quiet,?_⟩
  intro t
  exact (congrArg (LocalComparison.actualPush R.family N per j) (funext (shown t))).symm.trans (story.reads t)
end YM.Integration.WilsonOriginalTwoDateQHistory
