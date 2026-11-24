import YM.Integration.WilsonCapturedPrimaryOnRun
import YM.Integration.WilsonCapturedPrimaryWickTest
import YM.Integration.WilsonReceivedCenteredChart

/-! The actual original close post, including its full signed ordinary
pair and counterterm, tested on the real fields of the finite primary
decoder. All curve coefficients and the external radius use the same date. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryEnrolled
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
  (q : ℕ) (deep : 2*(q+1)+8 ≤ order) (aged : q+4 ≤ 3*k+2) {ε : ℝ} (ep : 0<ε)

theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (law : VowsR.LawScroll G φ) (enrolled : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay) (live : i<N) (fit : k≤R.alloy.B.a.clock.J i)
    (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical)

    (ready : ∀ (t : (Stock.census V).Mode) (v : V) (hv : v∈t.val),
      (eventually_atTop.mp (WilsonReceivedPaidCourse.original R simple D φ paid grades t v hv
        q 0 order shelf k seats deep aged 1 1 zero_le_one ep)).choose ≤ i)
    {d : ℕ} (frame : Labels.Frame G d) (A : Hol G) (T target v : ℕ) (extra : 1≤v)
    (funded : (eventually_atTop.mp (WilsonCapturedPrimaryReporter.panel R simple frame A T target v extra)).choose ≤ i)
    (support : 1≤(R.family.path.levels.budget i).supportExponent) (o : Site (R.family.side i per))
    (p : Probe G d) (hp : p∈tests frame)
    (a b c : V) (s : (Stock.census V).Mode) (distinct : a≠b) (pair : s.val={a,b})
    (x : Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices) :
    let budget := R.family.path.levels.budget i
    let rad := radius budget (cutoff budget g T)
    let δ := g^gap target v
    let bank := Air.craft P.model (fun j => (P.model j).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
    let program := (RunFormalChain.fromRun R).step N i per live
    let fieldD := WilsonCapturedPrimaryWickTest.fieldDegree order grades
    let y := WilsonCapturedPrimaryWickFiled.signed program F tag bank order fieldD d
      (WilsonCapturedPrimaryWickTest.directions A budget o rad p g) (g:ℂ) a b c s
    y.natDegree ≤ 2*(fieldD*d) ∧ ∀ t : ℝ,
      let angle := Stationary.arm G (R.family.side i per) 1 (lifted A budget o rad p g t)
      let U := WilsonCapturedPrimaryRays.field A budget o rad p t
      let W := Bulk.Fk program F tag bank angle order
      let Z := Order.value (g:ℂ) (Order.ratio W)
      let axis := (Stock.census V).fire
      y.eval (t:ℂ) = Z.part s-Z.part (axis c) ∧ (|t|≤2*δ →
        let Y := (((Ψ i).eval U:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i (physical x) U
        let M := Order.value (g:ℂ) (Order.logMarked W)
        let cost := fun l => (8*(budgetR R i)^seats*P.rent+ε*g^q)/(Poly.toll P.w l)
        let single := fun j => WilsonIndependentOrdinaryPairGrade.slot (axis j) (Order.render (Order.ratio W))
        ‖(Y.part s-Y.part (axis c))-y.eval (t:ℂ)‖ ≤
          (cost s+cost (axis c)+cost (axis a)*(‖M.part (axis b)‖+cost (axis b))+‖M.part (axis a)‖*cost (axis b)) +
          ‖(g:ℂ)‖^(order+1)*(WilsonIndependentOrdinaryPairGrade.mass (single a)*WilsonIndependentOrdinaryPairGrade.mass (single b))) := by
  intro budget rad δ bank program fieldD y
  have price := WilsonCapturedPrimaryWickTest.original program F tag bank A budget o rad p g order grades
    (fun j => le_rfl) a b c s distinct pair
  refine ⟨price.1, ?_⟩
  intro t angle U W Z axis
  refine ⟨price.2 t,?_⟩
  intro ht Y M cost single
  have geometry := (eventually_atTop.mp (WilsonCapturedPrimaryReporter.panel R simple frame A T target v extra)).choose_spec
    i funded p hp N per (by omega) support
  have gg : 0<g := geometry.1
  have small : ‖(g:ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos gg]
    exact geometry.2.1
  have paidCurve := WilsonCapturedPrimaryPotential.resolved A budget o rad p (cap:=1) gg zero_lt_one
    (t:=t) (ht.trans geometry.2.2.2.1) geometry.2.2.1
    ((mul_le_mul_of_nonneg_right ht (zero_le_one.trans (wallet_one A p rad))).trans geometry.2.2.2.2.1)
  have window := WilsonCapturedPrimaryPotential.window G budget gg (cap:=1) le_rfl
  have healthy : flags (Ψ i).p.threshold (Integral.sample g angle)=∅ := by
    rw [(course.1.walk i floor (Nat.le_of_lt live)).truep.point]
    exact paidCurve.2.1
  have result := WilsonReceivedCenteredChart.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
    seats i floor physical simple paid q deep aged ep course law enrolled fund live fit P 0 1 1 zero_le_one
    ready small a b c s distinct pair x F tag (lifted A budget o rad p g t) (bound G budget g 1)
    (by simpa only [abs_one,one_mul,pow_zero] using window) paidCurve.2.2 healthy
  rw [price.2 t]
  simpa only [paidCurve.1] using result

end YM.Integration.WilsonCapturedPrimaryEnrolled
