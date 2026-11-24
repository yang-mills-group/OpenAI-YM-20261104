import YM.Integration.WilsonCapturedPrimaryEnrolled
import YM.Integration.WilsonCapturedPrimaryPredictionMass
import YM.Integration.WilsonCapturedPrimaryPredictionPanel
import YM.Integration.WilsonCapturedPrimarySourceBudget

/-! One monetary invoice for the full signed ordinary reading at every
physical node, in the units of the pair and its counterterm on this post. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPredictionWindow
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter
open scoped Classical BigOperators Topology

open Labels Source Push.Local Next.Foundations Planned.AtomRegular
open WilsonCapturedPrimaryPaid WilsonCapturedPrimaryPotential WilsonCapturedPrimaryAngles WilsonCapturedPrimaryCollar WilsonCapturedPrimaryEstimate

variable {G : Gauge} (R : Run G) {m N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats i : ℕ) (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))

local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
variable (simple : G.Simple)
  (paid : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)

theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (law : VowsR.LawScroll G φ) (enrolled : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay) (live : i<N) (fit : k ≤ R.alloy.B.a.clock.J i)
    (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical)
    (logDate : (eventually_atTop.mp (WilsonReceivedLogWindow.original R simple D φ paid grades order shelf k seats 0 1 1 zero_le_one)).choose ≤ i)
    {d : ℕ} (frame : Labels.Frame G d) (A : Hol G) (T : ℕ)
    (enough : (eventually_atTop.mp (WilsonCapturedPrimaryReporter.panel R simple frame A T 0 1 (by decide))).choose ≤ i)
    (support : 1 ≤ (R.family.path.levels.budget i).supportExponent)
    (o : Site (R.family.side i per))
    (a b c : V) (s : (Stock.census V).Mode) (distinct : a≠b) (pair : s.val={a,b})
    (x : Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices) :
    let budget := R.family.path.levels.budget i
    let rad := radius budget (cutoff budget g T)
    let bank := Air.craft P.model (fun j => (P.model j).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
    let program := (RunFormalChain.fromRun R).step N i per live
    let D' := WilsonCapturedPrimaryWickTest.fieldDegree order grades
    let N' := 2*(D'*d)
    let y := fun p => WilsonCapturedPrimaryWickFiled.signed program F tag bank order D' d
      (WilsonCapturedPrimaryWickTest.directions A budget o rad p g) (g:ℂ) a b c s
    let σ := min (Poly.toll P.w s) (Poly.toll P.w ((Stock.census V).fire c))
    frame.coeffSize (frame.core (WilsonCapturedPrimaryDecoder.forecast frame y)) ≤
      WilsonCapturedPrimaryPredictionPanel.fee frame N'*(4/(σ*g^2)/(g^2)^d) := by
  intro budget rad bank program D' N' y σ
  have pos : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (RG02.Actual.coupling_pos R.makes.wilson live))
  have opp (p : Probe G d) (hp : p∈tests frame) := (eventually_atTop.mp
    (WilsonCapturedPrimaryReporter.panel R simple frame A T 0 1 (by decide))).choose_spec i enough p hp N per (by omega) support
  have rule (p : Probe G d) := WilsonCapturedPrimaryWickTest.original program F tag bank A budget o rad p g order grades
    (fun j => le_rfl) a b c s distinct pair
  have inv : d ≤ N' := by
    have one : 1 ≤ D' := by dsimp [D',WilsonCapturedPrimaryWickTest.fieldDegree];omega
    exact (Nat.le_mul_of_pos_left d (by omega : 0<D')).trans (by dsimp [N'];omega)
  have cool : g ≤ 1 := by
    have nonempty : (tests frame).Nonempty := by
      by_contra! h
      have impossible := (probe_budget frame).choose_spec.choose_spec.2 frame.e0 0 (le_refl 0) (by
        intro p hp;change p∈tests frame at hp;rw [h] at hp;exact False.elim (notMem_empty _ hp))
      rw [mul_zero] at impossible
      have zero : frame.e0=0 := norm_eq_zero.mp (le_antisymm ((norm_le_size frame _).trans impossible) (norm_nonneg _))
      have no := congrFun zero 0
      simp [Labels.Frame.e0] at no
    obtain ⟨p,hp⟩ := nonempty; exact (opp p hp).2.1
  have guard : 0 < σ := lt_min (Poly.worth P.salary.positive s) (Poly.worth P.salary.positive _)
  apply WilsonCapturedPrimaryPredictionPanel.priced frame y N' (fun p _ => (rule p).1) inv (sq_pos_of_pos pos)
    (pow_le_one₀ pos.le cool) (div_nonneg (by norm_num) (mul_pos guard (sq_pos_of_pos pos)).le)
  intro p hp j hj
  let z := g^2*WilsonFirstReceivedRadialStencil.node N' j
  have z0 : 0 ≤ z := mul_nonneg (sq_nonneg _) (WilsonFirstReceivedRadialStencil.node_mem hj).1
  have z1 : |z| ≤ 2*g^gap 0 1 := by
    rw [abs_of_nonneg z0]
    exact (mul_le_of_le_one_right (sq_nonneg g) (WilsonFirstReceivedRadialStencil.node_mem hj).2).trans
      (by change g^2 ≤ 2*g^2;linarith only [sq_nonneg g])
  have geo := opp p hp
  have curve := WilsonCapturedPrimaryPotential.resolved A budget o rad p (cap:=1) pos zero_lt_one
    (t:=z) (z1.trans geo.2.2.2.1) geo.2.2.1
    ((mul_le_mul_of_nonneg_right z1 (zero_le_one.trans (wallet_one A p rad))).trans geo.2.2.2.2.1)
  let mode := lifted A budget o rad p g z
  let angle := Stationary.arm G _ 1 mode
  let W := Bulk.Fk program F tag bank angle order
  have booked := (eventually_atTop.mp (WilsonReceivedLogWindow.original R simple D φ paid grades order shelf k seats
    0 1 1 zero_le_one)).choose_spec i logDate hk fit Q π Γ Ψ course books law enrolled fund floor live ahead actors
    pieces physical P x mode (bound G budget g 1)
    (by simpa only [abs_one,one_mul,pow_zero] using WilsonCapturedPrimaryPotential.window G budget pos (cap:=1) le_rfl)
    curve.2.2 F tag
  have unit : Order.UnitLeading W := Assembly.prescription_unit ..
  have sym : Order.Symmetric W := Assembly.prescription_sym (hv := program.positive F tag) ..
  have small : ‖(g:ℂ)‖ ≤ 1 := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos];exact cool
  have actual := WilsonCapturedPrimaryPredictionMass.priced W unit sym pos cool P.w P.salary.positive a b c s distinct pair
    (fun v => ⟨(booked v).1,(booked v).2 g small⟩)
  rw [(rule p).2 z]
  exact actual

end YM.Integration.WilsonCapturedPrimaryPredictionWindow
