import YM.Integration.WilsonPhysicalMarkedDefectGraph
import YM.Integration.WilsonPhysicalMarkedDefectSource
import YM.Integration.WilsonPhysicalMarkedDefectAllowance

/-! A one-step signed discrepancy on the *actual* receiving representation of
the given mixed physical course. The prescribed dressed entering painter has
zero prior marked ordinary remainder. Its independently submitted marked hard
input may still have all of its original coefficients. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect

open Function Filter Finset Lattice RG RG.Supply Precision Wilson Marker
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Ker
open Push ConnectedActivityE6 Input Org PhysicalNext PhysicalNext.Repeat Legato
open Uniform Next.SectorChange ThroughLaunch Pane AbsoluteSums PriceCompiler
open Primitives.TwoWave Primitives.TwoWave.RealSlice Kinetic.Port
open Progress.ClassicalKin Progress.ClassicalKin.Tent Pressure Next.Scheduling Next.Scheduling.Clock
open AnalyticBridge VerifiedReset Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open QuadraticLocal.Syl Comparison.RG02 Further.PhysicalPeriodLimitF933 Tree Oak QuadraticLocal.Rebirth
open FVA1Physical.MixedResets VowsR MintClock
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) (simple : G.Simple) {m n i k N : ℕ}
    (J : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) {Ψ : ∀ j, RG.Rep G (R.family.side j n)}
    (course : Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
    {φ : ℕ → ℕ} (scroll : LawScroll G φ) (clock : Offices.Books D R.rolls Q φ)
    (ahead : Mentor.Forecast D R.rolls Q φ clock)
    (quarterly : Oak.Tutoring.Quarterly R D Q scroll clock ahead)
    (regency : MintClock.Regency D R.rolls Q R.kit.target φ clock ahead R.alloy.delay)
    (hi : m ≤ i) (cut : i<N) (L : Lesson (N:=N) R J D Q π Γ hi)
    (school : School k) {V : Type} [Fintype V] [DecidableEq V]
    {marks : Census V} {T : V → Type} [∀ v, AddCommGroup (T v)] [∀ v, Module ℝ (T v)]
    (allow : ∀ v, Set (T v)) (kills : ∀ v, Submodule ℝ (T v)) (w : V → ℝ) (grades : V → ℕ)
    (η : ℝ) (s : ℕ) (hη : η ≤ 1/4) (schedule : Quark.Stature R school.pieces s η i ∧ Quark.Stature R (school.pieces+1) s η i)
    (f : Pupil (Ψ (i+1)) marks (Affinity.Wallet allow)) {priorCost : ℝ}
    (incoming : Ribbon (φ:=φ) R D Ψ allow kills grades school Set.univ w priorCost f)
    (x₀ : Affinity.Wallet allow)

set_option quotPrecheck false
local notation "fine" => (Ψ (i+1))
local notation "gf" => Coat.gStep (fine).beta
local notation "gc" => Coat.gStep (Ψ i).beta
local notation "stage" => (School.room school (PriceCompiler.step_paid R.alloy.B.a i)
  (J.trans (R.alloy.B.a.fits.mono hi)))
local notation "approved" => (School.future school (PriceCompiler.step_paid R.alloy.B.a i)
  (J.trans (R.alloy.B.a.fits.mono hi)) grades f.painter incoming.seed.total)
local notation "expense" => Oak.expenseReal R J D Q π Γ clock hi stage L ahead school.order school.horizon
local notation "rate" => ((2:ℝ)^((school.order:ℝ)+1-η) * gf^((school.order:ℝ)+1-η))
local notation "allowance" => emptyAllowance expense ((stage).count+1) rate
local notation "preModel" => (Oak.student (n:=n) R J D Q π Γ clock hi stage L ahead
  allow f.painter school.order approved)
local notation "postModel" => (Oak.Buffered.born (n:=n) R J D Q π Γ clock hi stage L ahead
  allow f.painter school.order approved)
local notation "residual" Z:max => (Mutation.grow preModel (Γ i) (Oak.grade0 R J D Q π Γ hi L)
  (Burn.horizon k+2) school.order gf gc (Ψ i) Z)
local notation "divisor" => LocalComparison.forcedDivisor R.family i
local notation "source" => (modelInput f.address fine marks (Affinity.Wallet allow)
  (originalHard f.packet x₀ incoming.seed.total.positive incoming.seed.policy))

include simple course scroll quarterly regency cut hη schedule x₀

/-- The held physical tests, presale, source graph, source forced array and both
original couplings precede the existential output. The output is the complete
native signed account on Ψᵢ (including its original unmarked K, every marked
hard row divided by `divisor`, support norms and scalar units). -/
theorem calibrated_empty
    (Z : Tint.Incoming f.address fine (Affinity.Wallet allow) Empty marks)
    (modes : Affinity.Crown f.address.support allow kills Z.hard)
    (hardPrice : Z.hard.Paid w (fine).p.B (fine).p.supportExponent 1) :
    ∃ (a : Type) (_ : Countable a) (E : Tint.Incoming (f.address.coarser (Route.step R i n).ratio)
      (Ψ i) (Affinity.Wallet allow) a marks),
      Calibrated R J D Q π Γ Ψ clock ahead hi L stage f.address allow kills f.painter Z w
        grades school.order school.horizon allowance 1 η s approved E ∧
      Full (Ψ i) w divisor (residual E) 2 (18*rate) ((2*gf)^(2*s)) := by
  obtain ⟨receiver⟩ := Oak.agrees R J D Q π Γ Ψ course hi cut L
  have hLevel : school.horizon ≤ R.alloy.B.a.clock.J i := le_trans (Nat.le_add_left ..)
    (le_trans school.tall (J.trans (R.alloy.B.a.fits.mono hi)))
  have fineBand : (fine).beta ∈ RG.Shoot.band R.alloy.B.a (i+1) :=
    (later R π Γ Ψ course (Nat.le_succ_of_le hi) cut).beta.symm ▸
      ((R.T.sticks N n).prices (i+1) (Nat.zero_le _) cut).2
  have hFine : 0 < gf := inv_pos.mpr (Real.sqrt_pos.mpr
    ((half_pos (PaceR.positive R (i+1))).trans_le fineBand.1))
  have hRate : 0 < rate := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hFine _)
  obtain ⟨hCost,hUnit,hPaid⟩ := empty_allowance expense ((stage).count+1) hRate
  have located : Affinity.Taut f.address.support allow kills Z.old := ⟨fun j=>j.elim,fun j=>j.elim⟩
  have zeroPrice := Spill.Foundry.empty_lit fine Z (fine).p.supportExponent (fine).p.B (w:=w)
  have entry := Lamps.loan_monotone Z.old zeroPrice hCost.le
  obtain ⟨a,count,E,both⟩ := Oak.Buffered.pares R simple J D Q π Γ Ψ course scroll clock
    quarterly.employed hi cut stage L receiver ahead quarterly.forecast allow kills f.painter Z w grades
    school.order school.horizon approved allowance 1 school.sense hLevel incoming.seed.total
    incoming.seed.school x₀ located modes hardPrice le_rfl hCost hUnit Set.univ quarterly.monthly
    school.price (Deletion.owed Set.univ Z.old entry) (Lamps.loan_monotone Z.old zeroPrice zero_le_one)
  letI := count
  have fee := Oak.Buffered.Phys.uphold R simple J D Q π Γ Ψ course scroll clock hi cut stage L ahead
    allow kills f.painter Z w grades school.order school.horizon approved allowance 1 school.sense
    hLevel incoming.seed.total le_rfl hCost quarterly regency η hη school.price schedule.1 schedule.2
    Set.univ E both
  have actual := post_price R J D Q π Γ Ψ course clock ahead hi cut L stage f.address
    allow kills f.painter Z w grades school.order school.horizon allowance 1 η s approved E
    both fee incoming.seed.total entry hardPrice
  exact ⟨a,count,E,actual,actual.late.enlarge hPaid le_rfl⟩

/-- Spatially supported dressed-graph input on the untouched true vacuum.
No previously emitted marked error appears on the right of the physical push.
The second conjunct is a forecast of the independently computed Wilson step on
the entering graph, evaluated after the original physical coupling change. -/
theorem calibrated_graph :
    ∃ (a : Type) (_ : Countable a) (E : Tint.Incoming (f.address.coarser (Route.step R i n).ratio)
      (Ψ i) (Affinity.Wallet allow) a marks),
      Full (Ψ i) w divisor (residual E) 2 (18*rate) ((2*gf)^(2*s)) ∧
      Renderer postModel (π i) (Step.tape (Burn.horizon k+2)) grades school.order
        (Route.reexpress R N (Burn.horizon k+2) (π (i+1)) f.painter school.order
          (Route.calibrator R D Q J π Γ hi L)) ∧
      ∀ x : Affinity.Wallet allow,
        (Route.step R i n).push (fine).beta (fun U => ((fine).eval U : ℂ) •
          Poly.pass ((rendered f.painter (fine).p gf).log x U)) =
            (Tint.Patrol.picture postModel (residual E)).density x := by
  let hard := originalHard f.packet x₀ incoming.seed.total.positive incoming.seed.policy
  have address := model_input_addresses (A:=f.address) (Γ:=marks) allow kills hard
  have price := model_input_prices (A:=f.address) (Γ:=marks) (X:=Affinity.Wallet allow) hard w
  obtain ⟨a,count,E,actual,bill⟩ := calibrated_empty R simple J D Q π Γ course scroll clock ahead
    quarterly regency hi cut L school allow kills w grades η s hη schedule f incoming x₀
    source address.2 price.2
  refine ⟨a,count,E,bill,actual.wilson.2,?_⟩
  intro x
  have field : (Tint.Patrol.picture f.painter source).density x = fun U => ((fine).eval U : ℂ) •
      Poly.pass ((rendered f.painter (fine).p gf).log x U) := by
    funext U
    apply model_input_field f.painter hard incoming.seed.total.positive
    exact ((rendered f.painter (fine).p gf).inlPaid w (source).old actual.billing.1).sums
      (fine).p.exponent_pos.le incoming.seed.total.positive x U
  rw [← field]
  exact ((actual.actual x).2.2.trans (actual.actual x).2.1).symm

end YM.Integration.WilsonPhysicalMarkedDefect

