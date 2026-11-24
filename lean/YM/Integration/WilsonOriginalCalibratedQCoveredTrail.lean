import YM.Integration.WilsonOriginalCalibratedQIndependentHistory
import YM.Integration.WilsonOriginalCoveredHearing

/-! The original two declared cohorts seed the complete independently computed signed history. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCalibratedQCoveredTrail
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
open FVA1Physical.TwoReset
open Function Filter Macrame Shingle
open AllOrder.Ker
open scoped Classical BigOperators Topology

open private trees tags from YM.Integration.WilsonOriginalCalibratedQIndependentHistory
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



local notation "oldCopy" h:max ν:max z:max => copyColor h (oldRows ν) grades (fun v=>((oldRows ν) v).paint (l z)) (π (j+1)) T₀
local notation "freshCopy" h:max z:max => WilsonOriginalCopiedQColor.color freshQ datum u η orders N h (rTest z) (π (j+1)) T₀

local notation "lowerStudent" T:max => Oak.student (n:=per) R hk D Q π Γ books floor (T).op (T).lesson ahead A₂ (T).model order (T).voter
local notation "namedInput" h:max ν:max z:max => WilsonOriginalJoinedCopyBank.joined old fresh mixGrades (oldCopy h ν z) (freshCopy h z)


local notation "courseLevel" => (show Burn.horizon k+2 ≤ R.alloy.B.a.clock.J (j+1) from hk.trans (R.alloy.B.a.fits.mono hi))
local notation "upperBook" => (litP D R.alloy Q courseLevel lesson.entry)
local notation "upperCoin" => Rebirth.caliber ((upperBook).issue lesson.entry) (((upperBook).sustenance.due lesson.entry).1)
local notation "uppers" ar:max how:max test:max => WilsonOriginalCopiedQColor.color upperQ upperDatum upperLabels
  upperFee upperOrders N (tiled R how ar) test (π ((j+1)+1)) T₀
local notation "values" gr:max how:max test:max => WilsonOriginalCoverCoefficient.read R cut order gr
  (fun ar=>uppers ar how test) (trees R (j+1) gr) (tags R (j+1) gr)
local notation "newOld" gr:max how:max test:max => WilsonOriginalCoverJetColors.colors (QuadraticLocal.Fk.money (π (j+1)) T₀)
  (fun s=>Sunrise.Launch.index (Stock.census V) grades s.val+1) order
  (WilsonOriginalCoverJetColors.reset order (values gr how test) ((upperCoin).back depth))
local notation "independent" gr:max how:max test:max => WilsonOriginalJoinedCopyBank.joined old fresh mixGrades
  (newOld gr how (l test)) (freshCopy how test)


local notation "coinAt" => WilsonOriginalCoveredEvolution.increment (Γ (j+1))
local notation "record" => Rebirth.caliber coinAt (by simp [WilsonOriginalCoveredEvolution.increment])
local notation "priorJet" gr:max how:max test:max => WilsonOriginalCoverJetColors.colors
  (QuadraticLocal.Fk.money (π (j+1)) T₀) (fun s=>Sunrise.Launch.index (Stock.census V) grades s.val+1) order
  (WilsonOriginalCoverJetColors.reset order (values gr how test) ((record).back depth))
local notation "sources" gr:max how:max test:max => WilsonOriginalJoinedCopyBank.joined old fresh mixGrades
  (priorJet gr how (l test)) (freshCopy how test)
local notation "declared" grid:max div:max datumX:max => WilsonOriginalCoverCoefficient.read R nextCut order grid
  (fun c=>sources (R.family.side (j+1) c.val) (tiled R div c) datumX)
  (WilsonOriginalCopiedHistory.forest R j grid) (WilsonOriginalCopiedHistory.tag R j grid)

include course cut pass in
/-- The original old and fresh physical source appointments compute this independently specified initial bank. -/
theorem entry (voter : ballot)
    (earned : Scene.Armada (studentOf voter) w grades σ (cost) order op.count shelf)
    (notes : Scene.Armada M w grades agenda b order op.count shelf)
    (S : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf op.count j floor physical)
    (passport : S.passport=joint) (names : S.modelIndex=namesOf voter) (table : HEq S.model (merged voter))
    (month : Scholar.Month R.rolls D Q R.alloy.delay) (fits : order≤Burn.horizon k+1)
    (narrow : shelf≤(A).clock.J (j+1)) (x : Wallet A₂)
    (grid : Side) (multiple : (R.family.side j per).val∣grid.val) (d : ℕ) (hd : d≤order)
    (y : Stationary.Link G grid) :
    (declared grid multiple x) d y=peek multiple (lowerStudent S) mixGrades (π (j+1)) T₀ x d y := by
  let zero := Oak.grade0 R hk D Q π Γ hi lesson
  have same : record=upperCoin := by
    have eqCoin : WilsonOriginalCoveredEvolution.increment (Γ (j+1))=(upperBook).issue lesson.entry :=
      (WilsonOriginalCoveredEvolution.measured (Γ (j+1)) zero).trans lesson.eats
    unfold Rebirth.caliber
    simp only [eqCoin]
  apply WilsonOriginalCoverCoefficient.identified
  rw [same]
  exact WilsonOriginalCalibratedQIndependentHistory.lower (R:=R) (course:=course) (cut:=cut)
    (pass:=pass) (voter:=voter) (earned:=earned) (notes:=notes) (S:=S) (passport:=passport)
    (names:=names) (table:=table) (month:=month) (fits:=fits) (narrow:=narrow) (x:=x) (grid:=grid)
    (multiple:=multiple) (F:=WilsonOriginalCopiedHistory.forest R j grid)
    (tag:=WilsonOriginalCopiedHistory.tag R j grid) (A₀:=y) (d:=d) (hd:=hd)

include course cut pass in
/-- At each reached date the starting two cohorts are still the inputs of the filed covered history. -/
theorem history (voter : ballot)
    (earned : Scene.Armada (studentOf voter) w grades σ (cost) order op.count shelf)
    (notes : Scene.Armada M w grades agenda b order op.count shelf)
    (S : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf op.count j floor physical)
    (passport : S.passport=joint) (names : S.modelIndex=namesOf voter) (table : HEq S.model (merged voter))
    (month : Scholar.Month R.rolls D Q R.alloy.delay) (fits : order≤Burn.horizon k+1)
    (narrow : shelf≤(A).clock.J (j+1)) (x : Wallet A₂)
    (shelved : shelf ≤ (A).clock.J m) {i : ℕ} {mi : Nat.le m i}
    {Y : Wallet A₂ → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {target : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades
      order shelf op.count i mi Y}
    (trail : WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf
      op.count floor physical S i mi Y target) :
    let start : WilsonOriginalCopiedHistory.Values G (Stock.census V) (R.family.side j per) :=
      fun grid div=>declared grid div x
    ∃ ij : i≤j, ∀ (g : ℂ) (y : Stationary.Link G (R.family.side i per)),
      WilsonCoherentMayerWindingGrades.panel order g (fun d=>WilsonOriginalCoveredEvolution.run
        R nextCut π Γ depth order mixGrades start i ij _ (dvd_refl _) d y) =
      let teacher := Oak.student (n:=per) R hk D Q π Γ books mi target.op target.lesson ahead A₂ target.model
        order target.voter
      WilsonCoherentMayerWindingGrades.panel order g (fun d=>Air.discharge
        (Air.craft teacher (fun a=>(teacher a).paint x) mixGrades (π i) T₀) d (Stationary.arm G _ 1 y)) := by
  intro start
  apply WilsonOriginalCoveredHearing.evaluated R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf
    op.count floor physical S x start nextCut course pass month fits shelved _ trail
  intro grid div d hd y
  exact entry (R:=R) (course:=course) (cut:=cut) (pass:=pass) (voter:=voter) (earned:=earned)
    (notes:=notes) (S:=S) (passport:=passport) (names:=names) (table:=table) (month:=month) (fits:=fits)
    (narrow:=narrow) (x:=x) (grid:=grid) (multiple:=div) (d:=d) (hd:=hd) (y:=y)

end YM.Integration.WilsonOriginalCalibratedQCoveredTrail
