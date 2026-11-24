import YM.Integration.WilsonCapturedPrimaryReturn
import YM.Integration.WilsonReceivedCloseOrdinaryPurchase

/-! Read one complete enrolled original pair minus its counterterm on each
date of its close interval, with its original source rent already restored. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryClose
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Pert.Asymptotics Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter
open scoped Classical BigOperators Topology
open Labels Source Push.Local Next.Foundations Planned.AtomRegular Trace.Physical.Germ
open WilsonCapturedPrimaryPaid WilsonCapturedPrimaryPotential WilsonCapturedPrimaryCollar

variable {G : Gauge} (R : Run G) (simple : G.Simple) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))
local notation "history" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "post" i:max f:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per

theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (initial : post b mb source) (top : b<N) {d : ℕ} (frame : Labels.Frame G d) (A : Hol G) (S : SectionData frame)
    (target u : ℕ) (a a' c : V) (s : (Stock.census V).Mode) (distinct : a≠a') (pair : s.val={a,a'})
    (δ : ℝ) (pos : 0 ≤ δ)
    (heard : WilsonReceivedCloseOrdinaryPurchase.Heard R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source initial top 0 1 1 c s (δ*(g b)^grade target d (u+1)))
    (calendar : (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ b)
    (late : (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple frame A S target u 1 le_rfl)).choose ≤ m) :
    ∀ i (ib : i ≤ b) (mi : m ≤ i), ∃ L : post i mi (history i ib),
      WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
        mb source initial i mi (history i ib) L ∧
      ∀ (x : Wallet actors) (F : Forest (move i).ratio) (tag : (move i).Choices)
        (o : Site (R.family.side i per)) (Z₀ : Coefficient frame (R.family.side i per)) (w κ s₀ C : ℝ),
      let budget := R.family.path.levels.budget i
      let high := grade target d (u+1)
      let rad := radius budget (cutoff budget (g (i+1)) (high+u))
      let bank := Air.craft L.model (fun j => (L.model j).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
      let program := (RunFormalChain.fromRun R).step N i per (ib.trans_lt top)
      let D' := WilsonCapturedPrimaryWickTest.fieldDegree order grades
      let N' := 2*(D'*d)
      let y := fun p => WilsonCapturedPrimaryWickFiled.signed program F tag bank order D' d
        (WilsonCapturedPrimaryWickTest.directions A budget o rad p (g (i+1))) (g (i+1):ℂ) a a' c s
      1 ≤ budget.supportExponent → d+1 ≤ budget.order →
      Readable A S (Ψ i).p (R.family.side i per) w → Z₀.Format o A (Ψ i) → Z₀.remBound o (Ψ i) κ s₀ →
      δ*3^high ≤ C → w*frame.coeffSize (frame.core Z₀.x)+s₀ ≤ C/(g (i+1))^u →
      (∀ U, Z₀.density o S (Ψ i) U = (LocalComparison.actualPush R.family N per i (((history i ib) x)) U).part s -
        (LocalComparison.actualPush R.family N per i (((history i ib) x)) U).part ((Stock.census V).fire c)) →
      frame.coeffSize (projection frame A (Ψ i).p.threshold o Z₀-WilsonCapturedPrimaryDecoder.forecast frame y) ≤ 
        WilsonCapturedPrimaryDecoder.invoice frame A N'*C*(g (i+1))^target := by
  intro i ib mi
  obtain ⟨L,record,output⟩ := heard i ib mi
  refine ⟨L,record,?_⟩
  intro x F tag o Z₀ w κ s₀ C budget high rad bank program D' N' y support rank read form hfee cash rough represented
  have date := (course.1.walk i mi (ib.trans top.le)).truep.point
  have heat : 0 < g (i+1) := inv_pos.mpr (Real.sqrt_pos.mpr (RG02.Actual.coupling_pos R.makes.wilson (ib.trans_lt top)))
  have birth : 0 < g b := inv_pos.mpr (Real.sqrt_pos.mpr (RG02.Actual.coupling_pos R.makes.wilson top.le))
  have comparable := WilsonReceivedCloseOrdinaryScale.inverse R simple (per:=per) ib top calendar
  have ratio : g b ≤ 3*g (i+1) := calc
    g b = (g (i+1))⁻¹*((g (i+1))*(g b)) := by field_simp
    _ ≤ (3*(g b)⁻¹)*((g (i+1))*(g b)) := mul_le_mul_of_nonneg_right comparable (mul_nonneg heat.le birth.le)
    _ = 3*g (i+1) := by field_simp
  have tol : δ*(g b)^high ≤ C*(g (i+1))^high := calc
    _ ≤ δ*(3*g (i+1))^high := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ birth.le ratio _) pos
    _ = (δ*3^high)*(g (i+1))^high := by rw [mul_pow,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right cash (pow_nonneg heat.le _)
  have cc : 0 ≤ C := (mul_nonneg pos (by positivity)).trans cash
  have inv : d ≤ N' := by
    have one : 1 ≤ D' := by dsimp [D',WilsonCapturedPrimaryWickTest.fieldDegree];omega
    exact (Nat.le_mul_of_pos_left d (by omega : 0<D')).trans (by dsimp [N'];omega)
  have price (p : Probe G d) := WilsonCapturedPrimaryWickTest.original program F tag bank A budget o rad p
    (g (i+1)) order grades (fun j => le_rfl) a a' c s distinct pair
  apply (WilsonCapturedPrimaryDecoder.returned frame A N' (projection frame A (Ψ i).p.threshold o Z₀) y
    (mul_nonneg cc (pow_nonneg heat.le target)) ?_).trans_eq (mul_assoc ..).symm
  have measured := (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple frame A S target u 1 le_rfl)).choose_spec
    i (late.trans mi) N per (by omega) support rank (Ψ i) date o Z₀ w κ s₀ C read form hfee cc rough N' inv y (fun p _ => (price p).1)
  intro test member
  rw [←mul_assoc]
  apply measured ?_ test member
  intro p hp j hj z mode angle window inside good
  let U := Integral.sample (g (i+1)) angle
  let Y := (((Ψ i).eval U:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i ((history i ib) x) U
  have same : WilsonCapturedPrimaryReading.reading S (Ψ i) o Z₀ U = Y.part s - Y.part ((Stock.census V).fire c) := by
    simp only [WilsonCapturedPrimaryReading.reading,represented U,Y,Poly.part_smul]
    ring
  have signed := output x F tag mode (bound G budget (g (i+1)) 1)
    (by simpa only [abs_one,one_mul,pow_zero] using window) inside good
  rw [same,(price p).2 z]
  exact signed.trans tol

end YM.Integration.WilsonCapturedPrimaryClose
