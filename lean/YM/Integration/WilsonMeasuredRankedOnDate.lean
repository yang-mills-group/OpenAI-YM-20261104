import YM.Integration.WilsonMeasuredRankedBooked
import YM.Integration.WilsonMeasuredDateRestriction
import YM.Integration.WilsonMeasuredRankedStore

/-! The full signed source budget on the selected original posts at the date
of this edge, uniformly over the distance from the original reporter. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredRankedOnDate
open Push.AbsoluteSums Next.Foundations
open Filter Labels Source Planned.GuardedAtom Push.Local
open WilsonOriginalReceivedChain
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Stationary Comparison.RG02 Comparison.RG02.Order Further.PhysicalPeriodLimitF933 Laurent
open WilsonMeasuredRankedResidual
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ j)
  (physical : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V))

  (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
    (floor.trans (Nat.le_succ j)) physical)

local notation "earlier" => (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x))
local notation "elected" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead order shelf
local notation "g" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta

local notation "stud" => Oak.student (n:=per) R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead actors P.model order P.voter
local notation "origin" => Oak.grade0 R hk D Q π Γ (floor.trans (Nat.le_succ j)) P.lesson
local notation "recorded" => Mutation.stamp stud (Γ (j+1)) origin (Burn.horizon k+2) order
local notation "inherited" => Mutation.grow stud (Γ (j+1)) origin (Burn.horizon k+2) order
  (Coat.gStep (Ψ ((j+1)+1)).beta) (Coat.gStep (Ψ (j+1)).beta) (Ψ (j+1)) P.output

variable (L : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor
  (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x)))
  (file : Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P L)
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (cut : j+1 < N)
  (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
  (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J (j+1)) (x : Wallet actors)

local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "depth" => (Burn.horizon k+2)
local notation "tape₀" => AllOrder.Floe.Step.tape depth
local notation "bankNow" => Air.craft L.model (fun v=>(L.model v).paint x) grades (π (j+1)) tape₀
local notation "priorBank" => Air.craft P.model (fun v=>(P.model v).paint x) grades (π ((j+1)+1)) tape₀
local notation "upperBank" => Air.craft stud (fun v=>((stud) v).paint x) grades (π (j+1)) tape₀
local notation "stampedBank" => Air.craft recorded (fun v=>((recorded) v).paint x) grades (π (j+1)) tape₀
local notation "gu" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "gl" => Coat.gStep (Ψ (j+1)).beta
local notation "older" => R.family.path.rep N per (j+1)
local notation "reverted" => Mutation.mend stud (Ψ (j+1)).p (Γ (j+1)) origin depth order gu gl
local notation "α" => (Ψ (j+1)).p.supportExponent+1+1

local notation "βh" => R.alloy.B.a.clock.hatBeta ((j+1)+1)
local notation "rp" => Ψ (j+1)
local notation "allowance" => R.alloy.B.a.clock.forcedAllowance (j+1)
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "roots" => (P.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "allFee" => (Spill.allOver (rp).p)^(order+shelf+1)

local notation "born" => (fun (x : Wallet actors) (U : Config G (R.family.side ((j+1)+1) per)) =>
  ((Ψ ((j+1)+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut P.model gu x U))
local notation "weights" => Stoop.radius P.w (elected^6)
local notation "pushFace" => LocalComparison.actualPush R.family N per (j+1) (born x)


open Pert.Asymptotics RG16 WilsonOlderSignedOneMarkPaid WilsonOlderSignedOneMarkTariff
open WilsonCenteredFiledAtoms
local notation "gm" => regulatorRun R.family N per j
local notation "Y₀" => R.family.params
variable (fieldRank : ℕ)
local notation "F₀" => R.family.labels.level fieldRank
local notation "S₀" => R.family.localSection fieldRank
local notation "base" => 2*Real.exp 102*(1+2*charge Y₀ S₀)
local notation "μ₀" => (R.family.path.levels.params (j+1)).columns

local notation "fixedP" => R.alloy.B.a.budget (j+1)
local notation "width" => Next.Foundations.price G (max (fixedP).order (fixedP).power)
local notation "wx" => WilsonMeasuredRankedPrimaryBudget.wrap F₀ Y₀

include file course cut pass month fits narrow in
theorem original
    (M₀:WilsonMeasuredRankedMenu.Menu R fieldRank) (office:M₀.onset≤j+1) (way : WayStation R.kit) (simple : G.Simple)
    (slow : ∀ n, ((R.family.S.block n).val:ℝ) ≤ Real.log (Lambda R.family.path.levels n))
    (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
    (fixed : (R.family.path.levels.budget (j+1)).supportExponent ≤ 100)
    (date : R.t fieldRank ≤ j+1) (late : WilsonCenteredCaptureClock.first R simple ≤ j+1)
    (grossDate : WilsonReceivedSourceGross.opening R simple ≤ j+1)
    (fareDate : WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared ≤ j+1)
    (scroll : VowsR.LawScroll G φ) (chamber : VowsR.Chamber scroll R.kit D Q books)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm : Spill.Raffle.Warm G D R.alloy.delay φ)
    (top : Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (load : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (d : ℕ) (space : Sycamore.Boot.need d
      (⟨order,seats,shelf,load,fits,packed⟩ : Syl.School k) ≤ R.alloy.B.a.clock.J ((j+1)+1))
    (q : ℕ) (ready : q+1+6 ≤ R.alloy.B.a.clock.J (j+1)) (deep : 2*(q+4+1)+8 ≤ order)
    (aged : q+4+4 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count (q+4) order k deep aged
      (tolerance_pos R fieldRank q (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep)) ≤ j+1)
    (recalled : WilsonCoherentMayerMutationIntake.firstDate R simple order (show (0:ℝ)<1 by norm_num)
      le_rfl (tolerance_pos R fieldRank q (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep)) ≤ j+1)
    (masks : WilsonOlderSignedOneMarkBooked.opening R simple (order+shelf+2) q 102
      (show 0 < WilsonMeasuredRankedMenu.fee R fieldRank M₀ ε/6 from div_pos (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep) (by norm_num)) ≤ j+1)
    (soft : WilsonOlderSignedOneMarkCurrency.opening R simple q (WilsonMeasuredRankedMenu.fee_positive R fieldRank M₀ ep) ≤ j+1) (v:V) :
    let u:=(Stock.census V).fire v
    let y:=roots v
    ∃ (A:Coefficient F₀ (R.family.side (j+1) per)) (b:ℝ), A.Format y Y₀ rp ∧ A.remBound y rp κ b ∧
      (∀ U,A.density y S₀ rp U=(pushFace U).part u-((rp).eval U:ℂ)*(Spill.Foundry.uncut L.model gl x U).part u) ∧
      P.w v*(b+(F₀).coeffSize A.x)≤ε*gm^q := by
  let hk' : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J j := hk.trans (R.alloy.B.a.fits.mono floor)
  let upper := WilsonMeasuredDateRestriction.post R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats (j+1) hi physical floor P (Nat.le_succ j)
  let lower := WilsonMeasuredDateRestriction.post R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats j floor earlier floor L (Nat.le_refl j)
  have refile : Filed R hk' D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      (Nat.le_refl j) physical upper lower :=
    ⟨file.passport,file.names,file.model,file.income,file.hard⟩
  have run:=WilsonMeasuredDateRestriction.course R π Γ Ψ floor course
  exact WilsonMeasuredRankedBooked.original R hk' D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats (Nat.le_refl j) physical upper lower refile run cut pass month fits narrow x
    fieldRank M₀ office way simple slow prepared fixed date late grossDate fareDate scroll chamber
    hospital warm top load packed d space q ready deep aged ep opened recalled masks soft v

end YM.Integration.WilsonMeasuredRankedOnDate
