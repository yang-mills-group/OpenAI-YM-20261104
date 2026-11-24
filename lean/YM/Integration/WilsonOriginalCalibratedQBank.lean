import YM.Integration.WilsonOriginalTwoDateFiledPost
import YM.Integration.WilsonReceivedCalibratedAppointment

/-! Identification of the complete deposited and freshly born input with the prescribed curvature banks on the same measured course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCalibratedQBank
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra
open QuadraticLocal.Rebirth ConnectedActivityE6 FullQLocal FullQLocal.RenderedStep
open Multi Exterior WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open private parts from YM.Integration.WilsonOriginalMixedFiniteMaterial
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
variable (initialRadius : V → ℝ)
local notation "w" => initialRadius
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


local notation "data₀" x => Air.craft M (fun a=>(M a).paint (l x)) grades (π ((j+1)+1)) T₀
local notation "read₀" x => testInclusion (ActualRunQlocalNativeTuple.orbit upperDatum) (l x)
local notation "packets₀" => ActualOriginalQPackets.packets upperQ upperDatum upperLabels upperFee upperOrders N
local notation "declared₀" x => NativePaidPacketColors.colors packets₀ (data₀ x).vac (read₀ x)
local notation "produced" ν:max x:max => Air.craft (studentOf ν) (fun a=>((studentOf ν) a).paint (l x)) grades (π (j+1)) T₀
local notation "deposited" ν:max x:max => Air.craft (oldRows ν) (fun a=>((oldRows ν) a).paint (l x)) grades (π (j+1)) T₀
local notation "newTest" x => testInclusion (ActualRunQlocalNativeTuple.orbit datum) (rTest x)
local notation "plant" ν:max x:max => NativePaidPacketColors.colors (ActualOriginalQPackets.packets freshQ datum u η orders N)
  (deposited ν x).vac (newTest x)
local notation "named" ν:max x:max => WilsonOriginalMixedFiniteMaterial.bank old fresh (deposited ν x) (plant ν x)
local notation "upperOp" => R.family.path.levels.clock.op (j+1) per
local notation "arm" => Stationary.arm G (R.family.side (j+1) per) 1
local notation "ledger" => litP D R.alloy Q (hk.trans ((A).fits.mono hi)) lesson.entry
local notation "back" => (Rebirth.caliber ((ledger).issue lesson.entry) ((ledger).sustenance.due lesson.entry).1).back depth
local notation "published" ν => Mentor.Cruise.publish D R.rolls Q R.alloy φ books op
  (Oak.era R hk D Q π Γ hi op lesson) (R.alloy.B.a.S.oneStep (j+1) per).exact_size M order ν lesson.entry

include course cut in
omit [Nonempty V] in
/-- The paid finite-to-cover seam at the old date has the actual declared upper Q
as input and the genuinely issued pre-reset analytic row as output. -/
theorem upper (voter : ballot)
  (earned : Scene.Armada (studentOf voter) w grades σ (cost) order op.count shelf)
    (notes : Scene.Armada M w grades agenda b order op.count shelf)
    (x:Wallet A₂) (F:Forest (upperOp).ratio) (tag:(upperOp).Choices)
    (T:Stationary.Link G (R.family.side (j+1) per)) (r:ℕ) (hr:r≤order) :
    (∀ g, g≠0 → ∀ U, Integral.markedLog g U (data₀ x)=Integral.markedLog g U (declared₀ x)) ∧
    ∃ δ:Poly (Stock.census V),
      Order.observe (Stock.census V) order (Order.logMarked (PhysicalWilsonPeriodizedMaterial.reference
        R N (j+1) per cut (arm T) (declared₀ x) order)) r=Air.discharge (produced voter x) r (arm T)+δ ∧
      Poly.price w δ ≤ Oak.Tutoring.bill R hk D Q π Γ books hi op lesson T b ∧
      HasSum (Alliance.miss M (fun a=>(M a).paint (l x)) (upperOp).ratio
         ((RunFormalChain.fromRun R).step N (j+1) per cut) F tag T (π ((j+1)+1)) T₀ (published voter) r) δ := by
  have legal : Legal T₀ (π ((j+1)+1)):=by
    rw [lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ lesson.entry
  have paid:=ActualOriginalQPackets.packets_paid upperQ upperDatum upperLabels upperFee upperOrders N
    (Ψ ((j+1)+1)).p (fun _=>1) 1 zero_lt_one (fun _=>zero_lt_one)
  have hg:=(IterationFour.Currency.g_pos R.makes N per ((j+1)+1) cut).ne'
  refine ⟨fun g h U=>?_,?_⟩
  · exact (WilsonOriginalClubSourcePackets.original upperQ upperDatum upperLabels upperFee upperOrders N
      agenda upperExtra (π ((j+1)+1)) T₀ (l x) (Ψ ((j+1)+1)).p g h U).trans
        (NativePaidPacketColors.colors_markedLog paid hg (data₀ x).vac (read₀ x) g h U).symm
  have declared:=(WilsonOriginalClubSourceReference.original upperQ upperDatum upperLabels upperFee upperOrders
    N agenda upperExtra (π ((j+1)+1)) T₀ (l x) cut legal (Ψ ((j+1)+1)).p F tag (arm T) order).2.2
  have rich : 1≤elected := (by norm_num : (1:ℝ)≤4).trans (MintClock.Page.roofers ..)
  obtain ⟨δ,reading,price,signed,_⟩:=(WilsonOriginalRosterFiniteMaterial.original R hk D Q π Γ Ψ course
    books hi cut op lesson ahead actors M w grades order shelf voter b notes (l x) F tag T (cost) earned
    (inv_le_one_of_one_le₀ rich)).2.2 r hr
  exact ⟨δ,declared ▸ reading,price,signed⟩

local notation "filed" T:max x:max => Air.craft (T).model (fun i=>((T).model i).paint x) mixGrades (π (j+1)) T₀

include course path cut sep pass in
/-- The full receiving table uses the independently deposited old row, the independently
specified new source and the measured kinetic reversion on every prior face. -/
theorem joined (voter : ballot)
  (earned : Scene.Armada (studentOf voter) w grades σ (cost) order op.count shelf)
    (S : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf op.count j floor physical)
  (bank : ∀ t, Air.craft S.model (fun i=>(S.model i).paint t) mixGrades (π (j+1)) T₀ =
    Air.craft (merged voter) (fun i=>((merged voter) i).paint t) mixGrades (π (j+1)) T₀)
    (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (load:op.count≤depth) (narrow:shelf≤(A).clock.J (j+1)) (fits:order≤Burn.horizon k+1)
    (packed:order+shelf≤depth)
    (late:WilsonOriginalMixedStampedFinite.firstDate R simple request freshQ u μ extra free D income K q freePos allow≤j)
    (Ω:ℝ) (one:1≤Ω) (cap:Ω≤page) (ordersOK:∀v,orders v≤K) (rank:ActualOriginalQLayout.rankCap R u≤order)
    (count:Fintype.card V≤op.count) (level:gradeTotal old grades tQ ≤ shelf) (x:Wallet A₂)
    (F:Forest (move).ratio) (tag:(move).Choices) (angle:fieldDir G (R.family.side j per) 1) (r:ℕ) :
    (filed S x).vac=(named voter x).vac ∧
    (∀ g, g≠0 → ∀ U, Integral.markedLog g U (filed S x)=Integral.markedLog g U (named voter x)) ∧
    (∀ g, g≠0 → ∀ U s, (Integral.markedLog g U (filed S x)).part s =
      (if s.val⊆old then (Integral.markedLog g U (deposited voter x)).part s else 0)+
      (if s.val⊆fresh then (Integral.markedLog g U (plant voter x)).part s else 0)) ∧
    Bulk.Fk ((RunFormalChain.fromRun R).step N j per nextCut) F tag (filed S x) angle r =
      Bulk.Fk ((RunFormalChain.fromRun R).step N j per nextCut) F tag (named voter x) angle r ∧
    ∀ (A' : Stationary.Link G (R.family.side (j+1) per)) n, n≤order → ∀ s:(Stock.census V).Mode,
      (Air.discharge (deposited voter x) n (arm A')).part s =
        Adjacent.born (fun d₀ a=>(Air.discharge (produced voter x) d₀ (arm a)).part s) back 0 order n A' := by
  rw [bank x]
  have result:=WilsonOriginalSignedDatedFinite.measured R simple request freshQ u μ extra free D income K q freePos allow
    hk Q π Γ Ψ course path books floor cut op lesson ahead actors M w grades order shelf voter sites orders old fresh sep
    l rTest x pass month (cost) earned load narrow fits packed late Ω one cap ordersOK rank count level F tag angle r
  obtain ⟨_,_,_,allField,finiteRead,_,reset,_⟩:=result
  refine ⟨rfl,allField,?_,finiteRead,reset⟩
  intro g h U s
  exact (congrArg (fun a : Poly (Stock.census V) => a.part s) (allField g h U)).trans
    (parts old fresh (deposited voter x) (plant voter x) sep g U s)

end YM.Integration.WilsonOriginalCalibratedQBank
