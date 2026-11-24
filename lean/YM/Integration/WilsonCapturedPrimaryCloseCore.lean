import YM.Integration.WilsonCapturedPrimaryReturn
import YM.Integration.WilsonCapturedPrimaryClose
import YM.Integration.WilsonCapturedPrimaryCoreBill
import YM.Trace.Physicalv2.GermPrices

/-! Read one complete enrolled original pair minus its counterterm on each
date of its close interval, with its original source rent already restored. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryCloseCore
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
    (target : ℕ) (a a' c : V) (s : (Stock.census V).Mode) (distinct : a≠a') (pair : s.val={a,a'})
    (δ : ℝ) (pos : 0 ≤ δ)
    (heard : WilsonReceivedCloseOrdinaryPurchase.Heard R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source initial top 0 1 1 c s (δ*(g b)^grade target d 1))
    (wrapped : (eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose ≤ m)
    (calendar : (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ b)
    (late : (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple frame A S target 0 1 le_rfl)).choose ≤ m) :
    ∀ i (ib : i ≤ b) (mi : m ≤ i), ∃ L : post i mi (history i ib),
      WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
        mb source initial i mi (history i ib) L ∧
      ∀ (x : Wallet actors) (F : Forest (move i).ratio) (tag : (move i).Choices)
        (o : Site (R.family.side i per)) (Z₀ : Coefficient frame (R.family.side i per)) (w κ s₀ : ℝ),
      let budget := R.family.path.levels.budget i
      let high := grade target d 1
      let rad := radius budget (cutoff budget (g (i+1)) high)
      let bank := Air.craft L.model (fun j => (L.model j).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
      let program := (RunFormalChain.fromRun R).step N i per (ib.trans_lt top)
      let D' := WilsonCapturedPrimaryWickTest.fieldDegree order grades
      let N' := 2*(D'*d)
      let y := fun p => WilsonCapturedPrimaryWickFiled.signed program F tag bank order D' d
        (WilsonCapturedPrimaryWickTest.directions A budget o rad p (g (i+1))) (g (i+1):ℂ) a a' c s
      1 ≤ budget.supportExponent → d+1 ≤ budget.order →
      Readable A S (Ψ i).p (R.family.side i per) w → Z₀.Format o A (Ψ i) → Z₀.remBound o (Ψ i) κ s₀ →
      (WilsonCapturedPrimaryDecoder.invoice frame A N'*(g (i+1))^target)*w ≤ 1/2 →
      (∀ U, Z₀.density o S (Ψ i) U = (LocalComparison.actualPush R.family N per i (((history i ib) x)) U).part s -
        (LocalComparison.actualPush R.family N per i (((history i ib) x)) U).part ((Stock.census V).fire c)) →
      frame.coeffSize (projection frame A (Ψ i).p.threshold o Z₀-WilsonCapturedPrimaryDecoder.forecast frame y) ≤ 
        2*(WilsonCapturedPrimaryDecoder.invoice frame A N'*(g (i+1))^target)*
          (δ*3^high+w*(frame.coeffSize (frame.core (WilsonCapturedPrimaryDecoder.forecast frame y))+
            WilsonCapturedPrimaryCoreBill.wrapFee frame A*s₀)+s₀) := by
  intro i ib mi
  obtain ⟨L,trail,priced⟩ := WilsonCapturedPrimaryClose.original R simple hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats mb source course initial top frame A S target 0 a a' c s distinct pair δ pos heard calendar late i ib mi
  refine ⟨L,trail,?_⟩
  intro x F tag o Z₀ w κ s₀ budget high rad bank program D' N' y support rank read form rem small represented
  have date := (course.1.walk i mi (ib.trans top.le)).truep.point
  have cap := (eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose_spec i (wrapped.trans mi) per
  have cold : wraps (Ψ i).p (R.family.side i per) ≤ 1 := by
    rw [date];simp only [zero_mul,Real.exp_zero] at cap;exact cap
  have xpos : 0 ≤ WilsonCapturedPrimaryDecoder.invoice frame A N' := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (sum_nonneg fun p _ => WilsonCapturedPrimaryPanel.fee_nonneg A p N')
  have heat : 0 ≤ g (i+1) := inv_nonneg.mpr (Real.sqrt_nonneg _)
  apply WilsonCapturedPrimaryCoreBill.paid frame A form rem read.order read.power cold _ read.nonneg
    (mul_nonneg xpos (pow_nonneg heat _)) (mul_nonneg pos (by positivity)) small
  intro C gate cash
  have bill := priced x F tag o Z₀ w κ s₀ C support rank read form rem gate (by simpa only [pow_zero,div_one] using cash) represented
  exact bill.trans_eq (by ring)

end YM.Integration.WilsonCapturedPrimaryCloseCore
