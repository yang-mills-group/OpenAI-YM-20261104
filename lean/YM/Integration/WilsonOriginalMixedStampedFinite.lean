import YM.Integration.WilsonOriginalMixedFiniteVoter
import YM.Integration.WilsonOriginalCompensatedSeat
import YM.Integration.WilsonOriginalMeasuredStampCoefficients

/-! On two adjacent dates of the actual course, retain the complete measured old rescaling and the independent fresh source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedStampedFinite
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

/-- Chosen solely from the original run and the submitted finite source bounds. -/
def firstDate : ℕ := (eventually_atTop.mp (Classical.choose_spec offer).2.choose_spec).choose

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
    order op.count op.stage k (R.alloy.B.a.clock.J (j+1))) (cost : ℝ) {a b : Type} (pieces : ∀ v, Submodule ℝ (X v))
  (Z : Tint.Incoming P (Ψ ((j+1)+1)) (Affinity.Wallet actors) a (Stock.census V))
  (rent : ℝ) (Y : Tint.Incoming (P.coarser (R.family.path.levels.clock.op (j+1) per).ratio)
    (Ψ (j+1)) (Affinity.Wallet actors) b (Stock.census V))
def Returned : Prop :=
  Oak.Buffered.SuccessStory (m:=m) (i:=j+1) (n:=per) (N:=N) (k:=k)
    (Θ:=V) (R₀:=Stock.census V) (K₁:=P) (W':=X) R hk D Q π Γ Ψ books (floor.trans (Nat.le_succ j))
    op lesson ahead actors pieces M Z w grades order shelf voter rent cost Y
local notation "M₁" => Oak.student (m:=m) (i:=j+1) (n:=per) (N:=N) (k:=k) R hk D Q π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead actors M order voter
local notation "ζ" => Oak.grade0 R hk D Q π Γ (floor.trans (Nat.le_succ j)) lesson
local notation "oldRows" => Mutation.stamp M₁ (Γ (j+1)) ζ depth order
local notation "file" => litP D R.alloy Q (hk.trans (R.alloy.B.a.fits.mono (floor.trans (Nat.le_succ j)))) lesson.entry
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "fig" => Oak.figureReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead order shelf
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead order shelf
local notation "rebate" => Oak.rebate R hk D Q π Γ (floor.trans (Nat.le_succ j)) op lesson
local notation "reserve" => WilsonOriginalCompensatedRadius.scale R j
local notation "charge" => (reserve)⁻¹*(rebate*((fig).produce (R.family.path.levels.clock.op (j+1) per).ratio.count*cost))
local notation "page" => WilsonMovingMentorPageRefund.cap R j
local notation "tQ" => (fun _ : V => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u)
variable (sites : V → Site (R.family.side (j+1) per)) (orders : V → ℕ)
local notation "datum" => ActualOriginalQPointSetup.pointDatum R request per (j+1) sites
local notation "η" => (μ+R.family.S.scale N-R.family.S.scale (j+1))-R.family.S.scale N
local notation "newRows" => WilsonOriginalProjectedCurvatureLamps.cohort freshQ datum u η orders N σ extra
variable {γ : Type} (old fresh : Finset V) (sep : Disjoint old fresh)
  (leftTest : γ → Affinity.Wallet actors) (rightTest : γ → tastes (ActualOriginalQPointSetup.pointDatum R request per (j+1) sites)) (x : γ)
local notation "mixGrades" => choice old grades tQ
local notation "test" => testInclusion (ActualRunQlocalNativeTuple.orbit datum) (rightTest x)
local notation "arm" => Stationary.arm G (R.family.side (j+1) per) 1
local notation "paidScale" => factor*(R.alloy.B.a.clock.hatBeta (j+1))^(exponent+1)

include course path in
theorem measured (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (previous : Returned R D hk Q π Γ Ψ books floor op lesson ahead actors M w grades order shelf voter cost pieces Z rent Y) (load : op.count ≤ depth) (narrow : shelf ≤ R.alloy.B.a.clock.J (j+1)) (fits : order ≤ Burn.horizon k+1)
    (packed : order+shelf ≤ depth) (oldPos : 0 ≤ cost) (oldPaid : cost ≤ (Ω₀)⁻¹)
    (late : firstDate R simple request freshQ u μ extra free D income K q freePos allow ≤ j)
    (Ω : ℝ) (one : 1 ≤ Ω) (cap : Ω ≤ page) (ordersOK : ∀ v, orders v ≤ K)
    (rank : ActualOriginalQLayout.rankCap R u ≤ order) (count : Fintype.card V ≤ op.count)
    (grade : gradeTotal old grades tQ ≤ shelf)
    (F : Forest (R.family.path.levels.clock.op j per).ratio) (tag : (R.family.path.levels.clock.op j per).Choices)
    (b₀ : fieldDir G (R.family.side j per) 1) (r : ℕ) :
    let school : Syl.School k := ⟨order, op.count, shelf, load, fits, packed⟩
    let nextOp := school.room (step_paid R.alloy.B.a j) (hk.trans (R.alloy.B.a.fits.mono floor))
    let regulatorPrice := paidScale
    let w₁ := fun v => free v/(regulatorPrice*Ω)
    let radius := Stoop.radius (choice old (Stoop.radius w reserve) w₁) 2
    let fee := (2:ℝ)⁻¹*(charge + Ω⁻¹)
    let previousRows := M₁
    let stamp := Mutation.stamp previousRows (Γ (j+1)) ζ depth order
    let freshRows := newRows
    let aggregate := WilsonMixedFaceLog.routed stamp freshRows old fresh sep leftTest rightTest
    let A₁ := Air.craft previousRows (fun v => (previousRows v).paint (leftTest x)) grades (π (j+1)) T₀
    let A₂ := Air.craft stamp (fun v => (stamp v).paint (leftTest x)) grades (π (j+1)) T₀
    let A₃ := Air.craft aggregate (fun v => (aggregate v).paint x) mixGrades (π (j+1)) T₀
    let Q₁ := NativePaidPacketColors.colors (ActualOriginalQPackets.packets freshQ datum u η orders N) A₂.vac test
    let actual := WilsonOriginalMixedFiniteMaterial.bank old fresh A₂ Q₁
    let form := (RunFormalChain.fromRun R).step N j per (Nat.lt_trans (Nat.lt_succ_self j) cut)
    let ledger := file
    Scene.Armada aggregate radius mixGrades σ fee order op.count shelf ∧ fee ≤ Ω⁻¹ ∧
      Mentor.Cruise.Voter aggregate σ order nextOp.count nextOp.stage k (R.alloy.B.a.clock.J j) ∧
      (∀ h, h ≠ 0 → ∀ U, Integral.markedLog h U A₃ = Integral.markedLog h U actual) ∧
      Bulk.Fk form F tag A₃ b₀ r = Bulk.Fk form F tag actual b₀ r ∧
      PhysicalWilsonPeriodizedMaterial.reference R N j per (Nat.lt_trans (Nat.lt_succ_self j) cut) b₀ A₃ r =
        PhysicalWilsonPeriodizedMaterial.reference R N j per (Nat.lt_trans (Nat.lt_succ_self j) cut) b₀ actual r ∧
      (∀ (A : Stationary.Link G (R.family.side (j+1) per)) n, n ≤ order → ∀ p : (Stock.census V).Mode,
        (Air.discharge A₂ n (arm A)).part p =
          Adjacent.born (fun e b => (Air.discharge A₁ e (arm b)).part p)
            ((Rebirth.caliber (ledger.issue lesson.entry) (ledger.sustenance.due lesson.entry).1).back depth) 0 order n A) ∧
      ∀ s : (Stock.census V).Mode, Poly.toll w₁ s * (regulatorPrice*Ω)^s.val.card = Poly.toll free s := by
  unfold Returned at previous
  intro school nextOp regulatorPrice w₁ radius fee previousRows stamp freshRows aggregate A₁ A₂ A₃ Q₁ actual form ledger
  have prior := WilsonOriginalCompensatedSeat.appointed R hk D Q π Γ Ψ course books (floor.trans (Nat.le_succ j)) cut op lesson ahead
    actors M w grades order shelf voter cost pieces Z rent Y pass month previous rfl floor load narrow fits packed oldPos oldPaid
  have budget := (eventually_atTop.mp (Classical.choose_spec offer).2.choose_spec).choose_spec j late
    k (hk.trans (R.alloy.B.a.fits.mono floor)) Ω one cap N per sites orders ordersOK (Nat.lt_trans (Nat.lt_succ_self j) cut)
  have accepted := budget.1 oldRows old fresh sep leftTest rightTest prior.1 school (le_refl _) rank count grade
    (prior.2.2.1 (zero_lt_one.trans_le one) cap)
  obtain ⟨second⟩ := Oak.tale R hk D Q π Γ floor (Nat.lt_trans (Nat.lt_succ_self j) cut) path
  have legal : Legal T₀ (π (j+1)) := by
    rw [second.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ second.entry
  have material := accepted.2.2.2 x (π (j+1)) T₀ legal (Ψ (j+1)).p F tag b₀ r
  have incurred := WilsonOriginalMeasuredStampCoefficients.original R hk D Q π Γ Ψ course books (floor.trans (Nat.le_succ j)) cut op lesson ahead
    actors M w grades order shelf voter pass month fits narrow _ previous.earning (leftTest x)
  exact ⟨accepted.1, accepted.2.1, accepted.2.2.1, material.2.2.1, material.2.2.2.1, material.2.2.2.2,
    incurred.2.2, fun s => (budget.2 s).1⟩

end YM.Integration.WilsonOriginalMixedStampedFinite
