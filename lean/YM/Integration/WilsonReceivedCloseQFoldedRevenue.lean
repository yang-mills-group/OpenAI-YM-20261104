import YM.Integration.WilsonReceivedCloseFoldedOrdinary
import YM.Integration.WilsonReceivedCloseQNamedTrail
import YM.Integration.WilsonOriginalCoveredHearing

/-! Original paid old and fresh Q insertions at both dates against their own independently named
folded ordinary table, with the signed angular winding and individual source refunds retained. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseQFoldedRevenue
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
open FVA1Physical.TwoReset
open Function Filter Macrame Shingle
open AllOrder.Ker
open private trees tags from YM.Integration.WilsonOriginalCalibratedQIndependentHistory
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

local notation "agenda" => QuadraticLocal.Poetry.Agenda.seed D φ (Burn.horizon k) ((A).clock.J ((j+1)+1))
local notation "upperDatum" => ActualOriginalQPointSetup.pointDatum R upperJ per ((j+1)+1) upperSites
local notation "upperFee" => (upperClock+R.family.S.scale N-R.family.S.scale ((j+1)+1))-R.family.S.scale N
local notation "actors" => WilsonOriginalProjectedCurvatureTableau.actors upperDatum
local notation "pieces₀" => (fun v=>(WilsonOriginalProjectedCurvatureTableau.nulls upperDatum v).restrictScalars ℝ)
local notation "M" => WilsonOriginalProjectedCurvatureLamps.cohort upperQ upperDatum upperLabels upperFee upperOrders N agenda upperExtra
local notation "grades" => (fun _ : V => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) upperLabels)

local notation "purchased" => WilsonReceivedCalibratedUpper.prepaid R simple upperJ upperQ upperLabels upperClock
  upperExtra upperFree D Q way ticket warm income books ahead education employment calendar hospital pass upperOrder upperPos

local notation "w" => (fun v=>upperFree v/((Classical.choose purchased)*((A).clock.hatBeta ((j+1)+1))^((Classical.choose_spec purchased).2.choose+1)*(elected)))

local notation "zeroA" => WilsonOriginalMixedTestTableau.zero upperDatum

local notation "fig" => Oak.figureReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead order shelf

local notation "tQ" => (fun _ : V => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u)
variable (sites : V → Site (R.family.side (j+1) per)) (orders : V → ℕ)
local notation "datum" => ActualOriginalQPointSetup.pointDatum R request per (j+1) sites
local notation "η" => (μ+R.family.S.scale N-R.family.S.scale (j+1))-R.family.S.scale N

variable (old fresh:Finset V) (sep:Disjoint old fresh)
local notation "freshA" => WilsonOriginalProjectedCurvatureTableau.actors datum
local notation "Knew" => (fun v=>(WilsonOriginalProjectedCurvatureTableau.nulls datum v).restrictScalars ℝ)
local notation "A₂" => WilsonMixedTestTableau.actors actors freshA
local notation "l" => WilsonMixedTestTableau.left actors freshA old zeroA
local notation "rTest" => WilsonMixedTestTableau.right actors freshA fresh (WilsonOriginalMixedTestTableau.zero datum)
local notation "mixGrades" => choice old grades tQ
local notation "sheet" => Pane.panel R.alloy (j+1) (R.alloy.B.a.S.oneStep (j+1) per).exact_size

local notation "hQ" => ActualOriginalQLayout.rankCap R u+Fintype.card V*WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u+1

local notation "incomeQ" => WilsonOriginalFreshQAtReceivedDate.prepaid R simple request freshQ u μ extra free D income warm K freePos

local notation "nextCut" => (Nat.lt_trans (Nat.lt_succ_self j) cut)
local notation "H" => Ψ (j+1)

local notation "fee" => QuadraticLocal.Earn.Invoice.price (H).p (fig).mist (order+shelf+1) op.count ((H).p.supportExponent+1+1) (fig).limitC G

local notation "raw" => ActualOriginalQInput.input upperQ upperDatum upperLabels upperFee upperOrders simple N (Nat.succ_le_of_lt cut)
local notation "prior" => fun x=> (sheet).push (Ψ ((j+1)+1)).beta (fun U=>((raw).leaf
  (testInclusion (ActualRunQlocalNativeTuple.orbit upperDatum) (l x))).density U)
local notation "physical" => fun x U=>Poly.pass (MergeProof.Accent.Mach (Stock.census V) (fun v =>
  ActualRunQlocalNativeTuple.reader datum v (testInclusion (ActualRunQlocalNativeTuple.orbit datum) (rTest x) v) *
    ActualOriginalCalibratedColumns.weightedObservable R B freshQ (u v) η (R.family.side i₁ per)
      (ActualRunQlocalNativeTuple.root datum v) U (orders v))) * (prior x U)

open QuadraticLocal.Affinity VowsR QuadraticLocal.Mentor

local notation "K₂" => WilsonMixedTestTableau.pieces pieces₀ Knew

local notation "g" => regulatorRun R.family N per

variable
  (protection : ∀ x k : ℕ, k ≤ x → ∀ β : ℝ, R.alloy.delay.betaEntry x ≤ β →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2) ≤ β)
  (prec span : ℕ) (deep : 2*(prec+1)+8 ≤ order) (aged : prec+4 ≤ 3*k+2)
  (height angleCap : ℝ) (capPos : 0 ≤ angleCap) {κ : ℝ} (kp : 0 < κ)

local notation "P₀" => Post (N:=N) R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf op.count j floor physical

local notation "d₀" => WilsonReceivedFirstQIncidence.degree ((Classical.choose_spec purchased).2.choose)
  exponent ((Classical.choose_spec incomeQ).2.choose) (QuadraticLocal.Spill.Raffle.pad hQ)
local notation "T₀₀" => WilsonReceivedFirstQIncidence.fee (Classical.choose purchased) factor (Classical.choose incomeQ) 1
local notation "fund₀" => max 1 ((T₀₀)*(8:ℝ)^d₀)
local notation "axes" => Fintype.card V

local notation "freshCopy" h:max z:max => WilsonOriginalCopiedQColor.color freshQ datum u η orders N h (rTest z) (π (j+1)) T₀

local notation "uppers" ar:max how:max test:max => WilsonOriginalCopiedQColor.color upperQ upperDatum upperLabels
  upperFee upperOrders N (tiled R how ar) test (π ((j+1)+1)) T₀
local notation "values" gr:max how:max test:max => WilsonOriginalCoverCoefficient.read R cut order gr
  (fun ar=>uppers ar how test) (trees R (j+1) gr) (tags R (j+1) gr)
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

local notation "cohort" => WilsonReceivedCloseQNamedBirth.Filed (R:=R) (simple:=simple)
    (request:=request) (freshQ:=freshQ) (u:=u) (μ:=μ) (extra:=extra) (D:=D) (hk:=hk) (Q:=Q)
    (π:=π) (Γ:=Γ) (Ψ:=Ψ) (books:=books) (floor:=floor) (cut:=cut) (op:=op) (lesson:=lesson)
    (ahead:=ahead) (income:=income) (way:=way) (ticket:=ticket) (warm:=warm) (education:=education)
    (employment:=employment) (calendar:=calendar) (hospital:=hospital) (pass:=pass)
    (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
    (upperExtra:=upperExtra) (upperOrder:=upperOrder) (order:=order) (shelf:=shelf)
    (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders)
    (old:=old) (fresh:=fresh) (sep:=sep)

local notation "heldPupil" age:max hm:max L:max => Oak.student (i:=age) (n:=per) R hk D Q π Γ books hm
  (L).op (L).lesson ahead A₂ (L).model order (L).voter

local notation "width" => (fund₀)*((g j)⁻¹)^(2*d₀+1)

local notation "sold₀" st:max => WilsonReceivedCloseNamedWallet.Sold R hk D Q π Γ Ψ books ahead A₂ K₂
  mixGrades order shelf op.count floor physical st Finset.univ width
local notation "served₀" st:max q:max ε:max => WilsonReceivedCloseOrdinaryRoster.Served R hk D Q π Γ Ψ books
  ahead A₂ K₂ mixGrades order shelf op.count floor physical st nextCut span height angleCap univ axes width
  ((g j)^(q+(2*d₀+1)*axes+1+axes)) (ε*(g j)^q)


local notation "canonical" => (fun (i:ℕ)(ib:i ≤ j) (x:Wallet A₂)(v:Stationary.Link G (R.family.side i per))(lag:ℕ) =>
  WilsonOriginalCoveredEvolution.run R nextCut π Γ depth order mixGrades (fun gr how=>declared gr how x)
    i ib (R.family.side i per) (dvd_refl _) lag v)
local notation "published" st:max => WilsonReceivedCloseQNamedTrail.Published (R:=R) (simple:=simple)
      (request:=request) (freshQ:=freshQ) (u:=u) (μ:=μ)
      (D:=D) (hk:=hk) (Q:=Q) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (books:=books)
      (floor:=floor) (cut:=cut) (op:=op) (ahead:=ahead) (upperJ:=upperJ) (upperQ:=upperQ)
      (upperLabels:=upperLabels) (upperClock:=upperClock) (order:=order) (shelf:=shelf)
      (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders) (old:=old)
      (fresh:=fresh) st
local notation "folded" st:max q:max eps:max => WilsonReceivedCloseFoldedOrdinary.Heard R hk D Q π Γ Ψ books ahead
  A₂ K₂ mixGrades order shelf op.count floor physical st nextCut canonical span height angleCap univ axes (2*d₀+1) q fund₀ eps

def Receipt (q:ℕ) (ε:ℝ) : Prop :=
  ∃start:P₀,sold₀ start ∧ served₀ start q (ε/2) ∧ published start ∧ folded start q ε

variable (q shape:ℕ) (cap ε:ℝ) (ep:0<ε)
local notation "gate" => WilsonReceivedCloseFoldedOrdinary.Ready (k:=k) R D (φ:=φ) mixGrades order shelf op.count
  simple axes (2*d₀+1) q shape span fund₀ cap height angleCap ε (le_max_left ..) capPos ep m

include course in
theorem original (law:VowsR.LawScroll G φ) (ch:VowsR.Chamber law R.kit D Q books)
    (volume:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (stage:k ≤ R.alloy.B.a.clock.J m) (close:PaceR.Close R shape cap m j) (dates:gate)
    (intake:∃start:P₀,sold₀ start ∧ served₀ start q (ε/2) ∧ published start) :
    Receipt (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ)
      (u:=u) (μ:=μ) (extra:=extra) (D:=D) (income:=income) (K:=K) (hk:=hk)
      (Q:=Q) (π:=π) (Γ:=Γ) (Ψ:=Ψ) (books:=books) (floor:=floor) (cut:=cut)
      (op:=op) (ahead:=ahead) (way:=way) (ticket:=ticket) (warm:=warm)
      (education:=education) (employment:=employment) (calendar:=calendar) (hospital:=hospital)
      (pass:=pass) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels)
      (upperClock:=upperClock) (upperExtra:=upperExtra) (upperOrder:=upperOrder)
      (order:=order) (shelf:=shelf) (upperSites:=upperSites) (upperOrders:=upperOrders)
      (sites:=sites) (orders:=orders) (old:=old) (fresh:=fresh)
      (span:=span) (height:=height) (angleCap:=angleCap) q ε := by
  obtain ⟨start,sold,served,pupil⟩:=intake
  refine ⟨start,sold,served,pupil,?_⟩
  have agree:WilsonReceivedCloseFoldedOrdinary.Match R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf op.count
      floor physical start canonical := by
    intro i mi ib L trail x field lag hl
    obtain ⟨ij,all⟩:=pupil i mi _ L trail x
    let n:=R.family.side i per
    let schol:=heldPupil i mi L
    have staff:=Air.license schol (fun v=>(schol v).paint x) mixGrades L.w L.issued.earning
      (Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)) (fun v=>L.issued.earning.honor v x)
    have same:=WilsonOriginalCopiedMarkerLayout.same (dvd_refl n.val) schol mixGrades (π (i+1)) (π i) T₀ x lag field staff
    exact (all n (dvd_refl _) lag hl field).trans (same.trans (WilsonOriginalSelfPeriod.original schol mixGrades (π i) T₀ x lag field staff))
  exact WilsonReceivedCloseFoldedOrdinary.original R hk D Q π Γ Ψ books ahead A₂ K₂ mixGrades order shelf op.count
    floor physical simple axes (2*d₀+1) q shape span fund₀ cap height angleCap ε (le_max_left ..) capPos ep
    start nextCut canonical course law ch volume stage agree univ _ served close dates

end YM.Integration.WilsonReceivedCloseQFoldedRevenue
