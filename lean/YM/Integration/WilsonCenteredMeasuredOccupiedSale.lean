import YM.Integration.WilsonCenteredOccupiedFare
import YM.Integration.WilsonCenteredReporterClock
import YM.Integration.WilsonCenteredIncomeRate
import YM.Integration.WilsonCenteredCourseKeeper
import YM.Integration.WilsonCenteredReceivedWages
import YM.Integration.WilsonCenteredCaptureClock
import YM.Integration.WilsonCenteredDetectorUnit

/-! The complete captured coefficient at polynomial cost on one original Wilson post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCenteredMeasuredOccupiedSale
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums Pert.Asymptotics RG16

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
local notation "modelFee" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G (sheet).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*P.cost) (Ω⁻¹*P.rent) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) oldG
local notation "account" => (Ω^6)⁻¹*(modelFee*((fig).produce (sheet).ratio.count*P.cost)+Ω^P.op.count*oldFee)
local notation "weights" => Stoop.radius P.w (Ω^6)

local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "configuration" => Config G (R.family.side i per)
local notation "value" => LocalComparison.actualPush R.family N per i

local notation "g" => regulatorRun R.family N per (i+1)
local notation "columns" => (R.family.path.levels.params i).columns
local notation "v" => R.alloy.B.a.clock.forcedAllowance i
local notation "p" => (Ψ i).p

include course cut in
theorem original (way : WayStation R.kit) (simple : G.Simple)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (early : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass : Pass D Q R.alloy R.kit) (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2)
    (s : (Stock.census V).Mode) (names : Finset V) (c : V→ℂ)
    (Z : Support (R.family.side i per)) (y : Site (R.family.side i per)) (rad u d r : ℕ) {α W : ℝ}
    (positive : 0≤W) (range : (p).supportExponent≤α) (near : rad≤(p).B) (house : Z⊆halo (p).B {y})
    (fixed : s.val.card≤r)
    (installed : ∀t:(Stock.census V).Mode,t.val⊆s.val→(Poly.toll weights t)⁻¹≤W*(g⁻¹)^u)
    (rest : ∀j∈names,(Poly.toll weights ((Stock.census V).fire j))⁻¹≤W*(g⁻¹)^u) :
    WilsonCenteredGalleryCapture.fare p (localSection G d) (hol G) weights s names c Z rad account κ v columns ≤
      (1+∑j∈names,‖c j‖)*(WilsonCenteredAllMaskCeiling.scale r*
        (WilsonCenteredPhysicalFare.base (localSection G d) (hol G) α W seats)^(3*r+9))/
        g^(WilsonCenteredPhysicalFare.degree seats u*(3*r+9)) :=by
  have clock := (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose_spec i early N per cut
  obtain ⟨temp,cap,move,field,live,small,hv,bill,forced⟩:=clock
  have point: p=R.family.path.levels.budget i := (course.1.walk i hi cut.le).truep.point
  have priced : account≤25*(2*(g⁻¹)^2)^(seats+1) :=
    (WilsonCenteredIncomeRate.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats
      physical P simple late pass hospital narrow load).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (R.alloy.B.a.fits.delayed (i+1)).le) cap _) (by norm_num))
  obtain ⟨positiveW,earned,-⟩:=WilsonCenteredReceivedWages.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf seats physical P way
  obtain ⟨_,_,_,bank⟩:=earned.budget
  have salary : 0≤account:=budget_nonneg (bank y)
  have e:=WilsonCenteredOccupiedFare.original p (localSection G d) (hol G) weights s names c Z y rad seats u r
    positiveW temp positive fixed range near house live small hv (point ▸ bill) (point ▸ forced) (point ▸ move)
    salary priced (zero_le_one.trans (R.family.path.levels.params i).columns_ge) field installed rest
  simpa only [div_eq_mul_inv,inv_pow] using e

end YM.Integration.WilsonCenteredMeasuredOccupiedSale
