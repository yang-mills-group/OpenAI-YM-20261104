import YM.Integration.WilsonCapturedPrimaryFundedPost
import YM.Integration.WilsonCapturedPrimaryDecoder

/-! Return the complete physical source in the original finite frame and
read the independently prescribed, normalized finite Wick moment on the same panel. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryReturn
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter
open scoped Classical BigOperators Topology

open Labels Source Push.Local Next.Foundations Planned.AtomRegular Trace.Physical.Germ
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
    {d : ℕ} (frame : Labels.Frame G d) (A : Hol G) (S : SectionData frame) (target u : ℕ)
    (room : grade target d (u+1)+2 ≤ q)
    (funded : (eventually_atTop.mp (WilsonCapturedPrimaryReporter.panel R simple frame A
      (grade target d (u+1)+u) target (u+1) (by omega))).choose ≤ i)
    (panel : (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple frame A S target u 1 le_rfl)).choose ≤ i)
    (support : 1≤(R.family.path.levels.budget i).supportExponent) (rank : d+1≤(R.family.path.levels.budget i).order)
    (K : RG.Rep G (R.family.side i per)) (date : K.p=R.family.path.levels.budget i) (vac : ∀ U, K.eval U=(Ψ i).eval U)
    (o : Site (R.family.side i per)) (Z₀ : Coefficient frame (R.family.side i per)) (w κ s₀ C Ĉ : ℝ)
    (read : Readable A S K.p (R.family.side i per) w) (form : Z₀.Format o A K) (hfee : Z₀.remBound o K κ s₀)
    (cc : 0≤C) (cap : 0≤Ĉ) (rough : w*frame.coeffSize (frame.core Z₀.x)+s₀ ≤ C/g^u)
    (a b c : V) (s : (Stock.census V).Mode) (distinct : a≠b) (pair : s.val={a,b})
    (x : Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices)
    (represented : ∀ U, Z₀.density o S K U = (LocalComparison.actualPush R.family N per i (physical x) U).part s -
      (LocalComparison.actualPush R.family N per i (physical x) U).part ((Stock.census V).fire c))
    (entrance : 8*(budgetR R i)^seats*P.rent+ε*g^q ≤ Ĉ*g^(grade target d (u+1)+2))
    (restored : 4*Ĉ+Ĉ^2+1 ≤ min (Poly.toll P.w s) (Poly.toll P.w ((Stock.census V).fire c))*C) :
    let budget := R.family.path.levels.budget i
    let high := grade target d (u+1)
    let rad := radius budget (cutoff budget g (high+u))
    let bank := Air.craft P.model (fun j => (P.model j).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
    let program := (RunFormalChain.fromRun R).step N i per live
    let D' := WilsonCapturedPrimaryWickTest.fieldDegree order grades
    let N' := 2*(D'*d)
    let y := fun p => WilsonCapturedPrimaryWickFiled.signed program F tag bank order D' d
      (WilsonCapturedPrimaryWickTest.directions A budget o rad p g) (g:ℂ) a b c s
    (∀ p∈tests frame, ‖runProbe frame p (projection frame A K.p.threshold o Z₀)-
      p.2.val.factorial*(y p).coeff p.2.val‖ ≤ WilsonCapturedPrimaryOriginal.fieldFee A p N'*C*g^target) ∧
    frame.coeffSize (projection frame A K.p.threshold o Z₀-WilsonCapturedPrimaryDecoder.forecast frame y) ≤
      WilsonCapturedPrimaryDecoder.invoice frame A N'*C*g^target := by
  intro budget high rad bank program D' N' y
  have expense (p : Probe G d) (hp : p∈tests frame) := WilsonCapturedPrimaryFundedPost.original R hk D Q π Γ Ψ books ahead
    actors pieces grades order shelf seats i floor physical simple paid q deep aged ep course law enrolled fund live fit P
    ready singleReady frame A (high+u) target (u+1) (by omega) funded support o p hp a b c s distinct pair x F tag
  let σ := min (Poly.toll P.w s) (Poly.toll P.w ((Stock.census V).fire c))
  have unit : 0 < σ := lt_min (Poly.worth P.salary.positive s) (Poly.worth P.salary.positive _)
  have inv : d≤N' := by
    have one : 1≤D' := by dsimp [D',WilsonCapturedPrimaryWickTest.fieldDegree];omega
    exact (Nat.le_mul_of_pos_left d (by omega : 0<D')).trans (by dsimp [N'];omega)
  have retrieved : ∀ p∈tests frame, ‖runProbe frame p (projection frame A K.p.threshold o Z₀)-
      p.2.val.factorial*(y p).coeff p.2.val‖ ≤ WilsonCapturedPrimaryOriginal.fieldFee A p N'*C*g^target := by
    apply (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple frame A S target u 1 le_rfl)).choose_spec
      i panel N per (by omega) support rank K date o Z₀ w κ s₀ C read form hfee cc rough N' inv y (fun p hp => (expense p hp).1)
    intro p hp j hj z mode angle window inside good
    have geom := (eventually_atTop.mp (WilsonCapturedPrimaryReporter.panel R simple frame A (high+u) target (u+1) (by omega))).choose_spec
      i funded p hp N per (by omega) support
    have positive : 0<g := geom.1
    have gp : 0<g^gap target (u+1) := pow_pos positive _
    have z0 : 0≤z := mul_nonneg gp.le (WilsonFirstReceivedRadialStencil.node_mem hj).1
    have z1 : |z|≤2*g^gap target (u+1) := by
      rw [abs_of_nonneg z0]
      exact (mul_le_of_le_one_right gp.le (WilsonFirstReceivedRadialStencil.node_mem hj).2).trans (by linarith only [gp])
    have field := (WilsonCapturedPrimaryPotential.resolved A budget o rad p (cap:=1) positive zero_lt_one
      (t:=z) (z1.trans geom.2.2.2.1) geom.2.2.1
      ((mul_le_mul_of_nonneg_right z1 (zero_le_one.trans (wallet_one A p rad))).trans geom.2.2.2.2.1)).1
    let U := WilsonCapturedPrimaryRays.field A budget o rad p z
    let Y := (((Ψ i).eval U:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i (physical x) U
    let E := 8*(budgetR R i)^seats*P.rent+ε*g^q
    have same : WilsonCapturedPrimaryReading.reading S K o Z₀ U = Y.part s - Y.part ((Stock.census V).fire c) := by
      simp only [WilsonCapturedPrimaryReading.reading,represented U,vac U,Y,Poly.part_smul]
      ring
    have gross := (expense p hp).2 z z1
    have enn : 0 ≤ budgetR R i := zero_le_one.trans (budget_pos R)
    have ep' : 0≤E := by dsimp [E];positivity [P.active]
    have spent := WilsonCapturedPrimarySourceBudget.paid high order positive geom.2.1 ep' cap entrance (by dsimp only [high];omega)
    have paid' : σ*‖Y.part s-Y.part ((Stock.census V).fire c)-(y p).eval (z:ℂ)‖ ≤ σ*(C*g^high) := by
      calc
        _ ≤ WilsonCapturedPrimarySourceBudget.cost g E order := gross
        _ ≤ (4*Ĉ+Ĉ^2+1)*g^high := spent
        _ ≤ (σ*C)*g^high := mul_le_mul_of_nonneg_right restored (pow_nonneg positive.le _)
        _ = _ := mul_assoc .. 
    have answer := (mul_le_mul_iff_right₀ unit).mp paid'
    change ‖WilsonCapturedPrimaryReading.reading S K o Z₀ (Integral.sample g (Stationary.arm G _ 1 (lifted A budget o rad p g z))) -
      (y p).eval (z:ℂ)‖ ≤ C*g^high
    rw [field,same]
    exact answer
  have gg : 0≤g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have measured := WilsonCapturedPrimaryDecoder.returned frame A N' (projection frame A K.p.threshold o Z₀) y
    (mul_nonneg cc (pow_nonneg gg _)) (fun p hp => by simpa only [mul_assoc] using retrieved p hp)
  exact ⟨retrieved,measured.trans_eq (mul_assoc ..).symm⟩

end YM.Integration.WilsonCapturedPrimaryReturn
