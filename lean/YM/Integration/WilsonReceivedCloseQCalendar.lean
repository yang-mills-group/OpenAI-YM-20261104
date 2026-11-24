import YM.Integration.WilsonReceivedCloseCalibratedMoments
/-! The actual original Q-source thresholds are elected before every upper cutoff, period, placement and width test. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseQCalendar
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


variable {k:ℕ} (Q : D.Tab R.rolls) (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  (way : WayStation R.kit) (ticket : TicketP R.alloy R.kit D Q)
  (warm : QuadraticLocal.Spill.Raffle.Warm G D R.alloy.delay φ)
  (education : Mentor.Educated D R.rolls Q R.kit.shape R.kit.scout φ books R.alloy.delay)
  (employment : ∀d,MintClock.Employment D φ d (R.rolls.L d))
  (calendar : MintClock.Regency D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (pass : Pass D Q R.alloy R.kit)
  (upperJ:Request V) (upperQ:MS.Land.Prescription B) (upperLabels:V→MS.Rake.Label B)
  (upperClock:ℝ) (upperExtra:V→ℕ) (upperOrder target order shelf:ℕ)
  (upperRank:ActualOriginalQLayout.rankCap R upperLabels ≤ order) (old:Finset V)
local notation "purchased" => WilsonReceivedCalibratedUpper.prepaid R simple upperJ upperQ upperLabels upperClock
  upperExtra free D Q way ticket warm income books ahead education employment calendar hospital pass upperOrder freePos
local notation "upperBank" => (Classical.choose_spec purchased).2.choose_spec order 0 target upperRank (zero_lt_one : (0:ℝ)<1)
local notation "hQ" => ActualOriginalQLayout.rankCap R u+Fintype.card V*WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u+1
local notation "incomeQ" => WilsonOriginalFreshQAtReceivedDate.prepaid R simple request freshQ u μ extra free D income warm K freePos
local notation "ut" => ((Classical.choose_spec purchased).2.choose+1)
local notation "ltoll" => max (exponent+1) ((Classical.choose_spec incomeQ).2.choose+1+QuadraticLocal.Spill.Raffle.pad hQ)
local notation "sourceOrder" => max ut ltoll
local notation "upperUnit" => 2*(Classical.choose purchased)*(8:ℝ)^ut
local notation "lowerUnit" => (max (2*factor) (Classical.choose incomeQ))*(4:ℝ)^ltoll
local notation "units" => max 1 (max (upperUnit) (lowerUnit))
local notation "mixGrades" => choice old (fun _:V=>WilsonOriginalProjectedCurvatureLoan.toll (R:=R) upperLabels)
  (fun _:V=>WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u)
variable (protection:∀ x k:ℕ,k ≤ x →∀ β:ℝ,R.alloy.delay.betaEntry x ≤ β →
  Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2) ≤ β)
  (prec span:ℕ) (deep:2*(prec+1)+8 ≤ order) (aged:prec+4 ≤ 3*k+2)
  (height angleCap:ℝ) (capPos:0 ≤ angleCap) {κ:ℝ} (kp:0<κ)
local notation "faceFee" n:max => 5*κ*(3:ℝ)^prec*(units)^n

private theorem rawDepth {p o:ℕ} (h:2*(p+1)+8 ≤ o) : 2*p+8 ≤ o := by omega
private theorem previousGrade {p k:ℕ} (h:p+4 ≤ 3*k+2) : p+3 ≤ 3*k+2 := by omega

/-- The two paid original wallet exponents at unit source load, fixed before the desired accuracy. -/
def birthOrder : ℕ := sourceOrder
def birthUnit : ℝ := units

variable (shape arity comparison:ℕ) {cap δ:ℝ} (cn:0≤cap) (dp:0<δ)
local notation "number" => Fintype.card V
local notation "logRead" => WilsonReceivedCloseSlate.opens R D mixGrades order shelf number simple protection
  prec span deep aged height angleCap capPos kp
local notation "massRead" => WilsonReceivedLogWindow.original R simple D φ protection mixGrades order shelf k
  number span height angleCap capPos
local notation "t₁" => (eventually_atTop.mp upperBank).choose
local notation "t₂" => WilsonOriginalMixedStampedFinite.firstDate R simple request freshQ u μ extra free D income
  K 0 freePos (zero_lt_one : (0:ℝ)<1)
local notation "t₃" => WilsonOriginalJointQWallet.firstBirth R simple request freshQ u μ extra free D income K freePos warm
local notation "t₄" => (eventually_atTop.mp (logRead)).choose
local notation "t₅" => WilsonReceivedMeasuredStampPrice.opening R simple prec order k
  (rawDepth deep) (previousGrade aged) kp
local notation "t₆" => WilsonReceivedCloseSignedPrice.opening R simple shape arity prec number cn
  («η»:=1) zero_lt_one kp.le
local notation "t₇" => (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple shape cap)).choose
local notation "t₈" => (eventually_atTop.mp (WilsonReceivedCloseCalibratedBudget.original R simple prec kp)).choose
local notation "t₉" => (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose
local notation "t₁₀" => (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose
local notation "t₁₁" => (eventually_atTop.mp (WilsonReceivedCloseEndpoint.original R simple (2*arity)
    («η»:=1) zero_lt_one)).choose
local notation "t₁₂" => (eventually_atTop.mp (WilsonReceivedCloseEndpoint.with_history R simple shape (2*2) 0
    cn («η»:=1) zero_lt_one (le_rfl : 0≤(0:ℝ)))).choose
local notation "t₁₃" => (eventually_atTop.mp (massRead)).choose
local notation "t₁₄" => (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
    (show 0 ≤ faceFee arity from mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) kp.le)
      (pow_nonneg (by norm_num) _)) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
    (zero_lt_one : (0:ℝ)<1))).choose
local notation "t₁₅" => (eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
    (WilsonReceivedCloseOrdinaryGrade.nonneg (Stock.census V) arity (2*sourceOrder+1) comparison
      (zero_le_one.trans (le_max_left 1 (max (upperUnit) (lowerUnit))))) dp)).choose

structure Window (base fine:ℕ) : Prop where
  upper : (t₁) ≤ fine+1
  fresh : (t₂) ≤ fine
  birth : (t₃) ≤ fine+1
  reading : (t₄) ≤ base
  stamp : (t₅) ≤ base+1
  signed : (t₆) ≤ fine
  clock : (t₇) ≤ fine
  rent : (t₈) ≤ fine
  nextHat : (t₉) ≤ fine
  cool : (t₁₀) ≤ fine
  endpoints : (t₁₁) ≤ fine
  swept : (t₁₂) ≤ fine
  mass : (t₁₃) ≤ base
  faceCharge : (t₁₄) ≤ fine
  ordinary : (t₁₅) ≤ fine

theorem original : ∀ᶠ base:ℕ in atTop,∀ fine,base ≤ fine →
    Window R simple request freshQ u μ extra D income K (k:=k) Q books
      ahead way ticket warm education employment calendar hospital pass upperJ upperQ upperLabels upperClock
      upperExtra upperOrder target order shelf upperRank old protection prec span deep aged height angleCap capPos
      kp shape arity comparison cn dp base fine := by
  filter_upwards [eventually_ge_atTop (t₁), eventually_ge_atTop (t₂), eventually_ge_atTop (t₃),
    eventually_ge_atTop (t₄), eventually_ge_atTop (t₅), eventually_ge_atTop (t₆), eventually_ge_atTop (t₇),
    eventually_ge_atTop (t₈), eventually_ge_atTop (t₉), eventually_ge_atTop (t₁₀), eventually_ge_atTop (t₁₁),
    eventually_ge_atTop (t₁₂), eventually_ge_atTop (t₁₃), eventually_ge_atTop (t₁₄),
    eventually_ge_atTop (t₁₅)] with base a b c d e f g h i j' k' l m' n o
  intro fine bf
  have next:=bf.trans (Nat.le_succ fine)
  exact ⟨a.trans next,b.trans bf,c.trans next,d,e.trans (Nat.le_succ base),f.trans bf,g.trans bf,
    h.trans bf,i.trans bf,j'.trans bf,k'.trans bf,l.trans bf,m',n.trans bf,o.trans bf⟩

end YM.Integration.WilsonReceivedCloseQCalendar
