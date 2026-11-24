import YM.Integration.WilsonOriginalCensusFiledTwoFlatCredit
import YM.Integration.WilsonOriginalOccupiedOptical

/-! Withdraw the complete earlier occupied credit at an actual clear field on the original optical corridor. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFiledClearCredit
open Filter MeasureTheory Multi
open Comparison.Density Comparison.Density.Transport Comparison.Density.Mirrors AnalyticBridge.SectorAffine.Offset
open MeasureTheory Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m   ≤   i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter

local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "lamps" => rendered student (Ψ i).p oldG
local notation "gauge" => Tint.Patrol.report student P.output oldG
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "cash" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G*
  ((fig).produce (sheet).ratio.count*P.cost)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "marks" => Stock.census V

open WilsonRootedKioskOccupiedSlip WilsonOriginalFlatFiledMask


open WilsonOriginalOrdinaryFlatHulls WilsonCapturedPrimarySoftPartition
open WilsonThermometerUnitFilingCoarse WilsonOriginalFlatOccupiedRate WilsonOriginalFlatFiledMask
open WilsonReceivedQuietCrownOwner OPE.Therm
local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "β" => R.alloy.B.a.clock.hatBeta i

private abbrev rowsOf {G : Gauge} {n : Side} {V X I : Type} [DecidableEq V] {o : V→Site n} {p : BudgetPoint}
    {U : Census V} (_ : Lamps X I G p o U) := I

open WilsonOriginalOccupiedCorridor WilsonOriginalOccupiedStencil
open private weaker from YM.Integration.WilsonOriginalOccupiedCorridor


variable (tariff:(Stock.census V).Mode→ℝ)
  (book:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books hi ahead actors pieces grades
    order shelf seats physical P tariff)


open WilsonOriginalOccupiedWindow Pert.Asymptotics
variable (simple:G.Simple)(n drift weight power:ℕ)(load:∀s:(Stock.census V).Mode,s.val.card ≤ n)
  (np:0 < n)(A η:ℝ)(A0:0 ≤ A)(positive:0 < η)
local notation "window" => WilsonOriginalOccupiedOptical.original R simple (marks) n drift weight power np load A η A0 positive

include cut in
theorem original (way:WayStation R.kit)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (ticket:TicketP R.alloy R.kit D Q){b:ℕ}(mb:m ≤ b)(bi:b ≤ i)(live:0 < i)
    (floor:(window).choose ≤ b)(late:(eventually_atTop.mp (window).choose_spec).choose ≤ i-1)
    (span:((i-b:ℕ):ℝ) ≤ A*(1+Real.log β)^drift)
    (pole q:ℕ)(sourced:∀t:(marks).Mode,(∑v∈t.val,grades v)+1 ≤ pole)
    (hardFloor:6*seats ≤ R.alloy.B.a.clock.J i)(deep:2*(q+1)+8 ≤ order)(aged:q+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0 < ε)(opened:WilsonFirstReceivedEarnedFee.opening R simple P.op.count q order k deep aged ep ≤ i)
    (x:Wallet actors)(s:(marks).Mode)(W:Config G (R.family.side b per))(clear:flags (Ψ b).p.threshold W=∅):
    let debt:=(8*Ω^P.op.count)*P.rent+ε*g^q
    let src:=Stoop.radius P.w (max 1 (cash+debt))
    let gain:=β^weight*Poly.toll src s
    let value:=‖WilsonOriginalOccupiedWindow.credit R (marks) (N:=N) bi Ψ (book.row x) s W‖
    let bank:=(η*(regulatorRun R.family N per i)^power)*(shards (marks) s).card
    gain*value ≤ bank ∧ (1 ≤ gain→value ≤ bank):=by
  have gates:=(eventually_atTop.mp (window).choose_spec).choose_spec (i-1) late
  rw [Nat.sub_add_cancel live] at gates
  intro debt src gain value bank
  letI:Countable P.outputIndex:=P.outputCount
  letI:Countable P.modelIndex:=P.modelCount
  letI : Countable (rowsOf (lamps)):=Scene.crewC P.model _ _ (Cruise.funded D R.rolls Q R.alloy φ books P.op
    (Oak.era R hk D Q π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model
    order P.voter P.lesson.entry P.lesson.studied ahead)
  letI:Nonempty (Wallet actors):=⟨x⟩
  obtain ⟨smooth,_,old,hard,field⟩:=WilsonOriginalFiledSuccessorIncome.original
    R hk D Q π Γ Ψ books hi cut ahead actors pieces grades order shelf seats physical P simple way course
    pole q sourced hardFloor deep aged ep opened
  let A_:=posted (lamps) P.output.old P.output.hard
  let factor₀:=max 1 (cash+debt)
  have one:1 ≤ factor₀:=le_max_left ..
  have pos:0 < factor₀:=zero_lt_one.trans_le one
  have hw:=P.issued.earning.positive
  have fresh:∀v,0 < src v:=fun v=> div_pos (hw v) pos
  have whole:A_.E.Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) (cash+debt):=Lamps.joinPaid smooth old
  have smaller:=Stoop.tighten P.w A_.E hw one whole
  have sale:factor₀⁻¹*(cash+debt) ≤ 1:=(inv_mul_le_one₀ pos).2 (le_max_right ..)
  have reg:=weaker A_.E src fresh (Lamps.loan_monotone _ smaller sale)
    (show (Ψ i).p.supportExponent ≤ (Ψ i).p.supportExponent+2 by linarith)

  have paid:=gates N per m k b cut.le bi floor mb
    span way D Q π Γ Ψ course ticket _ _ (homes) A_ src fresh reg (Stoop.leaves P.w A_.K hw one hard) x s W clear
  have full:(book.row x).A.density (book.row x).x=A_.density x:=(book.density x).trans (field x)
  have soft:(book.row x).A.E.log (book.row x).x=A_.E.log x:=book.mounted x
  dsimp only [gain,value,bank,WilsonOriginalOccupiedWindow.credit]
  rw [full,soft]
  exact paid

end YM.Integration.WilsonOriginalCensusFiledClearCredit
end
