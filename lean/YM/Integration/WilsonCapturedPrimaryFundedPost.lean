import YM.Integration.WilsonCapturedPrimaryEnrolled
import YM.Integration.WilsonCapturedPrimarySourceBudget

/-! One monetary invoice for the full signed ordinary reading at every
physical node, in the units of the pair and its counterterm on this post. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryFundedPost
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
    (singleReady : (eventually_atTop.mp (WilsonReceivedSingletonWindow.original R simple D φ paid
      grades order shelf k seats 0 1 1 zero_le_one)).choose ≤ i)
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
    let σ := min (Poly.toll P.w s) (Poly.toll P.w ((Stock.census V).fire c))
    let E := 8*(budgetR R i)^seats*P.rent+ε*g^q
    y.natDegree ≤ 2*(fieldD*d) ∧ ∀ t : ℝ, |t|≤2*δ →
      let U := WilsonCapturedPrimaryRays.field A budget o rad p t
      let Y := (((Ψ i).eval U:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i (physical x) U
      σ*‖(Y.part s-Y.part ((Stock.census V).fire c))-y.eval (t:ℂ)‖ ≤
        WilsonCapturedPrimarySourceBudget.cost g E order := by
  intro budget rad δ bank program fieldD y σ E
  have issue := WilsonCapturedPrimaryEnrolled.original R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i floor physical simple paid q deep aged ep course law enrolled fund live fit P
    ready frame A T target v extra funded support o p hp a b c s distinct pair x F tag
  refine ⟨issue.1,?_⟩
  intro t ht U Y
  let mode := WilsonCapturedPrimaryPotential.lifted A budget o rad p g t
  let angle := Stationary.arm G (R.family.side i per) 1 mode
  let W := Bulk.Fk program F tag bank angle order
  let axis := (Stock.census V).fire
  let single := fun j => WilsonIndependentOrdinaryPairGrade.slot (axis j) (Order.render (Order.ratio W))
  let L := Order.value (g:ℂ) (Order.logMarked W)
  have geometry := (eventually_atTop.mp (WilsonCapturedPrimaryReporter.panel R simple frame A T target v extra)).choose_spec
    i funded p hp N per (by omega) support
  have gg : 0<g := geometry.1
  have one : ‖(g:ℂ)‖ = g := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos gg]
  have small : ‖(g:ℂ)‖≤1 := one.trans_le geometry.2.1
  have curve := WilsonCapturedPrimaryPotential.resolved A budget o rad p (cap:=1) gg zero_lt_one
    (t:=t) (ht.trans geometry.2.2.2.1) geometry.2.2.1
    ((mul_le_mul_of_nonneg_right ht (zero_le_one.trans (wallet_one A p rad))).trans geometry.2.2.2.2.1)
  have training := (eventually_atTop.mp (WilsonReceivedSingletonWindow.original R simple D φ paid grades
    order shelf k seats 0 1 1 zero_le_one)).choose_spec i singleReady hk fit Q π Γ Ψ course books law enrolled
    fund floor live ahead actors pieces physical P x mode (WilsonCapturedPrimaryPotential.bound G budget g 1)
    (by simpa only [abs_one,one_mul,pow_zero] using WilsonCapturedPrimaryPotential.window G budget gg (cap:=1) le_rfl)
    curve.2.2 F tag
  have wallet (j : V) : Poly.toll P.w (axis j)=P.w j := by simp [Poly.toll,axis,Census.fire]
  have pairW : Poly.toll P.w s=P.w a*P.w b := by simp [Poly.toll,pair,distinct]
  have positive : 0≤E := by
    have enn : 0 ≤ budgetR R i := zero_le_one.trans (budget_pos R)
    dsimp only [E]
    positivity [P.active]
  have bounded (j : V) : g*(P.w j*WilsonIndependentOrdinaryPairGrade.mass (single j)) ≤ 1 ∧
      g*(P.w j*‖L.part (axis j)‖) ≤ 1 := by
    have backed := training j
    change g*(Poly.toll P.w (axis j)*WilsonIndependentOrdinaryPairGrade.mass (single j)) ≤ 1 ∧
      ∀ z : ℂ, ‖z‖≤1 → g*(Poly.toll P.w (axis j)*‖(Order.value z (Order.logMarked W)).part (axis j)‖) ≤ 1 at backed
    rw [wallet j] at backed
    exact ⟨backed.1,backed.2 _ small⟩
  have fees (j : V) : 0 ≤ WilsonIndependentOrdinaryPairGrade.mass (single j) :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have observed := (issue.2 t).2 ht
  change ‖(Y.part s-Y.part (axis c))-y.eval (t:ℂ)‖ ≤
    (E/(Poly.toll P.w s)+E/(Poly.toll P.w (axis c))+
    E/(Poly.toll P.w (axis a))*(‖L.part (axis b)‖+E/(Poly.toll P.w (axis b)))+
    ‖L.part (axis a)‖*(E/(Poly.toll P.w (axis b)))) +
    ‖(g:ℂ)‖^(order+1)*(WilsonIndependentOrdinaryPairGrade.mass (single a)*WilsonIndependentOrdinaryPairGrade.mass (single b)) at observed
  simp only [pairW,wallet,one] at observed
  have result := WilsonCapturedPrimarySourceBudget.complete order gg positive
    (P.salary.positive a) (P.salary.positive b) (P.salary.positive c)
    (fees a) (fees b) (norm_nonneg (L.part (axis a))) (norm_nonneg (L.part (axis b)))
    (bounded a).1 (bounded b).1 (bounded a).2 (bounded b).2 observed
  change min (Poly.toll P.w s) (Poly.toll P.w (axis c))*_ ≤ _
  rwa [pairW,wallet]

end YM.Integration.WilsonCapturedPrimaryFundedPost
