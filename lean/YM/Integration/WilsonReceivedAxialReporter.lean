import YM.Integration.WilsonReceivedSourceGross
import YM.Integration.WilsonReceivedAxialExtension
import YM.Integration.WilsonReceivedAxialCurrency
import YM.Integration.WilsonRegisteredAxialChart
import YM.Integration.WilsonRegisteredAxialRoom

/-! A real locally cold reporter receives the full issued rooted marked
coefficient with arbitrary exterior. One onset covers all placements,
all source tests and both regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedAxialReporter
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Ac OPE.Therm WilsonLimitConstruction RG16 MSbar.Heath Labels Source Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare
open scoped Classical BigOperators Topology

def opening {G : Gauge} (R : Run G) (simple : G.Simple) {η : ℝ} {T : Campaign R}
    {W : Campaign.Pillars R T} (funded : FundedOriginalProperties.{u} simple η W)
    (slow : ∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J : Voice G) (clear : Clear G J) (n q base : ℕ) {ε : ℝ} (ep : 0 < ε) : ℕ :=
  max (WilsonReceivedSourceGross.opening R simple)
    (max ((eventually_atTop.mp (WilsonReceivedAxialCurrency.price R simple funded n q ep)).choose)
      (max ((eventually_atTop.mp (WilsonRegisteredAxialRoom.torus R simple (q+2*n) (base+1))).choose)
        ((eventually_atTop.mp (WilsonRegisteredAxialChart.fit R simple slow J clear (q+2*n) base)).choose+1)))

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

local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "a" => ((Ψ i).p.supportExponent+1+1)
local notation "fee" => ((Spill.allOver (Ψ i).p)^(order+shelf+1)*Ω)

local notation "placed" => P.passport.coarser (R.family.path.levels.clock.op i per).ratio
local notation "n" => (order+shelf+2)

include course cut in
theorem original (simple : G.Simple) {η : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (funded : FundedOriginalProperties.{u} simple η W)
    (slow : ∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J : Voice G) (clear : Clear G J) (axes : Lattice.Order) (q base : ℕ) {ε : ℝ} (ep : 0 < ε)
    (late : opening R simple funded slow J clear n q base ep ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) :
    let H := radius R (q+2*n) (base+1) i
    let r := amplitude R J H N per i
    let τ := angularCut (R.family.path.levels.clock.hatBeta i)
    ∀ (v : V) (U : Config G (R.family.side i per)),
      U ∈ House.chilly (WilsonAxialWindow.cells ((placed).origin v) H) τ →
      ∃ ξ : Directions G (R.family.side i per),(∀ e, ‖ξ e‖ ≤ (Ψ i).p.threshold) ∧
        (Ψ i).p.dirBound ((placed).origin v) ξ ∧
        (∀ z ∈ Set.Icc (0:ℝ) r,∀ Y : Support (R.family.side i per),
          Healthy (Ψ i).p.threshold Y (increment 1 (z • ξ))) ∧
        ∀ (t : Wallet actors) (s : (Stock.census V).Mode),v∈s.val →
          Poly.toll P.w s*‖(bare lamps t U).part s-(bare lamps t (increment 1 (r • ξ))).part s‖ ≤
            ε*(regulatorRun R.family N per i)^q := by
  intro H r τ v U cold
  obtain ⟨lg,lr⟩ := max_le_iff.mp late
  obtain ⟨lc,lr'⟩ := max_le_iff.mp lr
  obtain ⟨ltor,lchart⟩ := max_le_iff.mp lr'
  have cal := (eventually_atTop.mp
    (WilsonRegisteredAxialChart.fit R simple slow J clear (q+2*n) base)).choose_spec
  have predecessor := Nat.le_sub_one_of_lt lchart
  have back : i-1+1=i := by omega
  have fit := cal (i-1) predecessor N per (by rw [back];exact cut.le)
  rw [back] at fit
  obtain ⟨rp,weak,chart,logarithm,rad,stay⟩ := fit
  have point : (Ψ i).p = R.family.path.levels.budget i := (course.1.walk i hi cut.le).truep.point
  have physicalPoint : (Ψ i).p = (R.family.path.rep N per i).p :=
    point.trans (R.makes.wilson.represents N per i cut.le).vac.symm
  let b := WilsonDegreeFourInheritedRange.height R (q+2*n) i
  have place : b*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B < H := by
    rw [point]
    change _ < base+1+b*(4*R.family.path.levels.clock.coverSize i+2)+2*R.family.path.levels.clock.coverSize i
    change b*(4*R.family.path.levels.clock.coverSize i+2)+2*R.family.path.levels.clock.coverSize i < _
    omega
  have room := (eventually_atTop.mp
    (WilsonRegisteredAxialRoom.torus R simple (q+2*n) (base+1))).choose_spec i ltor per
  change 10*H < _ at room
  have smallRoom : 2*H < (R.family.side i per).val := by omega
  have Gs := WilsonReceivedSourceGross.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces
    grades order shelf seats physical P simple lg pass hospital narrow load
  have hn : 0 ≤ fee := mul_nonneg (pow_nonneg (zero_le_one.trans (Spill.allOver_ge _)) _)
    P.issued.Waffle.paysAbove.le
  have ha : 0 ≤ a := by linarith only [(Ψ i).p.exponent_pos]
  have accepted := WilsonReceivedAxialExtension.locally lamps P.issued.earning.positive ha Gs.1
    J clear axes v b H place smallRoom weak rp U cold chart
    (by simpa only [physicalPoint] using logarithm) (by simpa only [physicalPoint] using rad) stay
  obtain ⟨ξ,uniform,cost,healthy,data⟩ := accepted
  refine ⟨ξ,uniform,cost,healthy,?_⟩
  intro t s hs
  have pay := (eventually_atTop.mp (WilsonReceivedAxialCurrency.price R simple funded n q ep)).choose_spec
    i lc N per cut a (by rw [←physicalPoint];linarith) fee hn Gs.2
    (Poly.toll P.w s*‖(bare lamps t U).part s-(bare lamps t (increment 1 (r • ξ))).part s‖)
  exact pay (by simpa only [mul_assoc] using data t s hs)
end YM.Integration.WilsonReceivedAxialReporter
