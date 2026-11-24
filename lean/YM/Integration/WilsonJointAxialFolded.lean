import YM.Integration.WilsonReceivedSourceGross
import YM.Integration.WilsonJointAxialRoster
import YM.Integration.WilsonReceivedAxialFiling
import YM.Integration.WilsonReceivedAxialCurrency
import YM.Integration.WilsonRegisteredAxialChart
import YM.Integration.WilsonRegisteredAxialRoom

/-! One physical group configuration and the independent cover bank tested
on one common field for all genuine sets of occupied names. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonJointAxialFolded
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
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "placed" => P.passport.coarser (R.family.path.levels.clock.op i per).ratio
local notation "n" => (order+shelf+2)
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "stage" => R.alloy.B.a.clock.J i
local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)

open WilsonJointAxialRoster

include course cut in
theorem selected (simple : G.Simple) {η : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (funded : FundedOriginalProperties.{u} simple η W)
    (slow : ∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J : Voice G) (clear : Clear G J) (axes : Lattice.Order) (q : ℕ) {ε : ℝ} (ep : 0 < ε)
    (width : ∀ j k : ℕ, k ≤ j → ∀ b : ℝ, R.alloy.delay.betaEntry j ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) j)⁻¹ ^ 2) ≤ b)
    (late : max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card V) n q ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width order shelf (Fintype.card V) ep) ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) (fit : k ≤ stage) :
    let H := radius R (invoice (Fintype.card V) (q+2*n)) 1 i
    let r := amplitude R J H N per i
    let τ := angularCut (R.family.path.levels.clock.hatBeta i)
    ∀ U : Config G (R.family.side i per), U ∈ House.chilly (plaquettes (placed).origin H) τ →
      let ξ := WilsonJointAxialWindow.direction (placed).origin
          ((WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1) J axes r U;
        
        let A := WilsonCapturedPrimaryPotential.potential gf (r • ξ)
        let angle := Stationary.arm G (R.family.side i per) 1 A
        Integral.sample gf angle = increment 1 (r • ξ) ∧ 0 ≤ r ∧ r ≤ 1 ∧
        (∀ e,‖ξ e‖ ≤ (Ψ i).p.threshold) ∧
        (∀ z ∈ Set.Icc (0:ℝ) r,∀ Y : Support (R.family.side i per),
          Healthy (Ψ i).p.threshold Y (increment 1 (z • ξ))) ∧
        ∀ (x : Wallet actors) (s : (Stock.census V).Mode), s.val.Nonempty →
          let writer := Air.craft student (fun b => (student b).paint x) grades (π i) tape
          let folded := WilsonCoherentMayerWindingGrades.panel order (gf:ℂ) (fun j => Air.discharge writer j angle)
          Poly.toll P.w s*‖(bare lamps x U).part s-folded.part s‖ ≤
            ε*(regulatorRun R.family N per i)^q + ε*gf^order := by
  intro H r τ U cold
  obtain ⟨left,right⟩ := max_le_iff.mp late
  let ξ := WilsonJointAxialWindow.direction (placed).origin
          ((WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1) J axes r U
  obtain ⟨r0,r1,capped,healthy,_,gaps⟩ :=
    WilsonJointAxialRoster.selected R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf seats physical P simple funded slow J clear axes q ep left pass hospital narrow load U cold
  obtain ⟨sampling,filed⟩ := WilsonReceivedAxialFiling.tested R hk D Q π Γ Ψ course books hi cut ahead
    actors pieces grades order shelf seats physical P simple width ep right fit ξ capped r0 r1
  refine ⟨sampling,r0,r1,capped,healthy,?_⟩
  intro x s marks writer folded
  let L := (bare lamps x U).part s
  let M := (bare lamps x (increment 1 (r • ξ))).part s
  have tol := (Poly.worth P.issued.earning.positive s).le
  calc
    Poly.toll P.w s*‖L-folded.part s‖ ≤ Poly.toll P.w s*(‖L-M‖+‖M-folded.part s‖) :=
      mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using dist_triangle L M (folded.part s)) tol
    _ = _ := mul_add ..
    _ ≤ _ := add_le_add (gaps x s marks) (filed x s)
include course cut in
theorem original (simple : G.Simple) {η : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (funded : FundedOriginalProperties.{u} simple η W)
    (slow : ∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J : Voice G) (clear : Clear G J) (axes : Lattice.Order) (q : ℕ) {ε : ℝ} (ep : 0 < ε)
    (width : ∀ j k : ℕ, k ≤ j → ∀ b : ℝ, R.alloy.delay.betaEntry j ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) j)⁻¹ ^ 2) ≤ b)
    (late : max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card V) n q ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width order shelf (Fintype.card V) ep) ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) (fit : k ≤ stage) :
    let H := radius R (invoice (Fintype.card V) (q+2*n)) 1 i
    let r := amplitude R J H N per i
    let τ := angularCut (R.family.path.levels.clock.hatBeta i)
    ∀ U : Config G (R.family.side i per), U ∈ House.chilly (plaquettes (placed).origin H) τ →
      ∃ ξ : Directions G (R.family.side i per),
        let A := WilsonCapturedPrimaryPotential.potential gf (r • ξ)
        let angle := Stationary.arm G (R.family.side i per) 1 A
        Integral.sample gf angle = increment 1 (r • ξ) ∧ 0 ≤ r ∧ r ≤ 1 ∧
        (∀ e,‖ξ e‖ ≤ (Ψ i).p.threshold) ∧
        (∀ z ∈ Set.Icc (0:ℝ) r,∀ Y : Support (R.family.side i per),
          Healthy (Ψ i).p.threshold Y (increment 1 (z • ξ))) ∧
        ∀ (x : Wallet actors) (s : (Stock.census V).Mode), s.val.Nonempty →
          let writer := Air.craft student (fun b => (student b).paint x) grades (π i) tape
          let folded := WilsonCoherentMayerWindingGrades.panel order (gf:ℂ) (fun j => Air.discharge writer j angle)
          Poly.toll P.w s*‖(bare lamps x U).part s-folded.part s‖ ≤
            ε*(regulatorRun R.family N per i)^q + ε*gf^order := by
  intro H r τ U cold
  exact ⟨WilsonJointAxialWindow.direction (placed).origin
          ((WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1) J axes r U,
    selected R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats physical P
    simple funded slow J clear axes q ep width late pass hospital narrow load fit U cold⟩

end YM.Integration.WilsonJointAxialFolded
