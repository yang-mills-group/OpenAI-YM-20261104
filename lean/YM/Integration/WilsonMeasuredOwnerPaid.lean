import YM.Integration.WilsonMeasuredOwnerRank
import YM.Integration.WilsonMeasuredOwnerFare
import YM.Integration.WilsonMeasuredRankedMenu

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerPaid
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Pert.Asymptotics RG16
open Push.AbsoluteSums Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph RG16.Guarding
open ProjectorNext.Equivariance

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
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
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)

local notation "weights" => Stoop.radius P.w (Ω^6)
local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "debt" => (⟨P.output.old,P.output.hard⟩ :
  Gallery (Wallet actors) P.outputIndex homes (Ψ i) (Stock.census V))
local notation "βhat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta


variable (rank:ℕ)
local notation "F₀" => R.family.labels.level rank
local notation "S₀" => R.family.localSection rank
local notation "Y₀" => R.family.params
local notation "μ₀" => Next.Foundations.price G (max (Ψ i).p.order (Ψ i).p.power)
local notation "wp" => R.alloy.B.a.clock.forcedAllowance i


local notation "cash" => WilsonMeasuredRankedResidual.sourceCost R rank
local notation "wrap" => WilsonMeasuredRankedPrimaryBudget.wrap (F₀) Y₀

include course cut in
/-- Restore the original incidence width only after pricing the joint physical
coefficient, including its nonzero ranked primary and the complete hard exit. -/
theorem original [Nonempty V] (cost:P.cost=0) (M:WilsonMeasuredRankedMenu.Menu R rank)
    (simple:G.Simple) (way:WayStation R.kit)
    (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (prepared:WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed:(R.family.path.levels.budget i).supportExponent ≤ 100)
    (date:R.t rank ≤ i) (active:M.onset ≤ i)
    (late:WilsonCenteredCaptureClock.first R simple ≤ i)
    (gross:WilsonReceivedSourceGross.opening R simple ≤ i)
    (fare:WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared ≤ i)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (shelved:shelf ≤ R.alloy.B.a.clock.J i) (load:P.op.count ≤ Burn.horizon k+2)
    (q:ℕ) (ready:q+6 ≤ R.alloy.B.a.clock.J i) (deep:2*(q+4+1)+8 ≤ order)
    (aged:q+4+4 ≤ 3*k+2)
    (opening:WilsonFirstReceivedEarnedFee.opening R simple P.op.count (q+4) order k deep aged
      (show (0:ℝ)<1 by norm_num) ≤ i)
    (cool:gf ≤ 1) (rent:(8*Ω^P.op.count)*P.rent ≤ gf^(q+4))
    (x:Wallet actors) (v:V) :
    let y:=homes v
    let u:=(Stock.census V).fire v
    ∃ (A:Coefficient F₀ (R.family.side i per)) (b:ℝ),
      A.Format y Y₀ (Ψ i) ∧ A.remBound y (Ψ i) κ b ∧
      (∀U,A.density y S₀ (Ψ i) U=(LocalComparison.actualPush R.family N per i (physical x) U).part u) ∧
      P.w v*(b+(F₀).coeffSize A.x) ≤ WilsonMeasuredOwnerFare.unitCost cash M.cost wrap q * gf^q := by
  intro y u
  let E:=(8*Ω^P.op.count)*P.rent+gf^(q+4)
  let b:=WilsonOlderSignedSingletonFare.fare (Ψ i).p S₀ Y₀ weights u 1 {y} 0
    ((Ω^6)⁻¹*E) (βhat^(-((q+6:ℕ):ℝ))*κ) κ wp (R.family.path.levels.params i).columns
  have nr:=WilsonMeasuredOwnerRank.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces
    grades order shelf seats physical P rank cost way simple late (q+4) (q+6) ready deep aged
    (show (0:ℝ)<1 by norm_num) opening date x v
  simp only [one_mul] at nr
  obtain ⟨A,shape,paid,profile,primary⟩:=nr
  have native:=(course.1.walk i hi cut.le).truep.point
  have ⟨gp,clock⟩:=WilsonMeasuredRankedPrimaryBudget.native R simple cut per
  have Ωp:=P.issued.Waffle.paysAbove
  have ep:0 ≤ E:=add_nonneg (mul_nonneg (by positivity) P.active.le) (pow_nonneg gp.le _)
  have raw:=WilsonMeasuredRankedFare.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf seats physical P rank simple slow prepared fixed gross fare pass hospital shelved load v E ep q
  have hb:P.w v*b ≤ cash*(gf⁻¹)^4*E+2*Real.exp 102*(2*gf^2)^q:=by
    simpa only [b,u,y,WilsonMeasuredRankedResidual.sourceCost,Poly.solo_toll] using raw
  have bn:0 ≤ b:=by
    obtain ⟨a1,a2,h1,h2,amt,-⟩:=paid
    change a1+a2 ≤ b at amt
    linarith only [h1,h2,amt]
  have hp:0 ≤ R.alloy.B.a.clock.hatBeta i:=le_of_lt (zero_lt_one.trans (R.alloy.B.a.fits.delayed i))
  have mpos:0 ≤ M.cost:=M.positive.le
  obtain ⟨f1,f2⟩:=M.slots i active y
  have rankPrice:=WilsonMeasuredRankedPrimaryBudget.scalar (Ψ i).p Y₀ S₀ y μ₀
    (θ:=P.w v) (b:=b) (net:=(F₀).coeffSize A.x) (f:=M.cost*R.alloy.B.a.clock.hatBeta i)
    (P.issued.earning.positive v) ep bn (by rw [native];exact fixed)
    (by simpa only [native] using f1) (by simpa only [native] using f2)
    (mul_nonneg mpos hp) primary
  refine ⟨A,b,shape,paid,profile,?_⟩
  apply WilsonMeasuredOwnerFare.paid q gp cool (WilsonMeasuredRankedResidual.sourceCost_pos R rank).le
    hp mpos (mul_nonneg (WilsonMeasuredRankedGerm.wrapCost_nonneg ..) (Real.exp_pos _).le) clock ?_ hb rankPrice
  dsimp only [E]
  linarith only [rent]

end YM.Integration.WilsonMeasuredOwnerPaid
