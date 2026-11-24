import YM.Integration.WilsonReceivedCloseSignedPrice
import YM.Integration.WilsonReceivedPaidCourse

/-! Signed comparison with the independently filed finite block along an enrolled Wilson close history. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseSigned
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per

variable (simple : G.Simple) (s : (Stock.census V).Mode) (v : V) (inside : v ∈ s.val)
  (protection : ∀ x k : ℕ, k ≤ x → ∀ β : ℝ, R.alloy.delay.betaEntry x ≤ β →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2) ≤ β)
  (q span : ℕ) (deep : 2*(q+1)+8 ≤ order) (aged : q+4 ≤ 3*k+2)
  (H angleCap : ℝ) (capPos : 0 ≤ angleCap) {ε : ℝ} (ep : 0 < ε)
local notation "audience" => WilsonReceivedPaidCourse.original R simple D φ protection grades s v inside
  q span order shelf k seats deep aged H angleCap capPos ep

include mb in
theorem original (P₀ : P b mb source)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (top : b < N)
    (pass : Pass D Q R.alloy R.kit) (scroll : VowsR.LawScroll G φ)
    (chamber : VowsR.Chamber scroll R.kit D Q books) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J m)
    (load : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (unit : ε ≤ 1) (fitStage : k ≤ R.alloy.B.a.clock.J m)
    (openRead : (eventually_atTop.mp audience).choose ≤ m)
    (late : WilsonReceivedMeasuredStampPrice.opening R simple q order k (by omega) (by omega) ep ≤ m+1)
    (test : Wallet actors) (degree a : ℕ) (occupied : s.val.card ≤ a) {cap η : ℝ} (cn : 0 ≤ cap) (loss : 0 < η)
    (ready : WilsonReceivedCloseSignedPrice.opening R simple degree a q seats cn loss ep.le ≤ b)
    (close : PaceR.Close R degree cap m b) :
    ∀ i (ib : i ≤ b) (mi : m ≤ i), ∃ L : P i mi (read i ib),
      WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
        mb source P₀ i mi (read i ib) L ∧
      ∀ (x : Wallet actors) (F : Forest (move i).ratio) (tag : (move i).Choices)
        (A : Stationary.Link G (R.family.side i per)) (z : ℝ),
        let B := R.family.path.levels.budget i
        let angle := Stationary.arm G (R.family.side i per) 1 A
        |z| ≤ |H| * (Real.log (R.family.path.levels.clock.hatBeta i))^span*((B.B:ℝ)^2*B.threshold)/(g (i+1)) →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ angleCap * |z|) →
        let W := Integral.sample (g (i+1)) angle
        flags (Ψ i).p.threshold W=∅ →
        let actual := Order.logTo (Fintype.card V) ((((Ψ i).eval W:ℂ)⁻¹) •
          LocalComparison.actualPush R.family N per i ((read i ib) x) W)
        let bank := Air.craft L.model (fun j => (L.model j).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let step := (RunFormalChain.fromRun R).step N i per (ib.trans_lt top)
        let value := Order.value (g (i+1):ℂ) (Order.logMarked (Bulk.Fk step F tag bank angle order))
        Poly.toll P₀.w s*‖(actual-value).part s‖ ≤ (g b)^(-η)*(P₀.rent+2*ε*(3*g b)^q) := by
  intro i ib mi
  obtain ⟨L,history,price⟩ := WilsonReceivedCloseSignedPrice.paid R hk D Q π Γ Ψ books ahead
    actors pieces grades order shelf seats mb source P₀ course path top pass scroll chamber month hospital
    fits narrow load packed simple q (by omega) (by omega) ep unit late test degree a cn loss ready close i ib mi
  refine ⟨L,history,?_⟩
  intro x F tag A z B angle bounded controls W clear
  have hearing := (eventually_atTop.mp audience).choose_spec i (openRead.trans mi) hk
    (fitStage.trans (R.alloy.B.a.fits.mono mi)) Q π Γ Ψ course books scroll chamber fund mi
    (ib.trans_lt top) L.op L.capacity L.lesson ahead actors L.model L.w L.voter L.cost L.salary
    x F tag A pieces L.input L.rent L.output L.issued L.affordable z bounded controls clear
  rw [L.represented x] at hearing
  exact price s occupied _ hearing

end YM.Integration.WilsonReceivedCloseSigned
