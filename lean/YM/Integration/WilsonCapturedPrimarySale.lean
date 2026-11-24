import YM.Integration.WilsonCapturedPrimaryReturn
import YM.Integration.WilsonCapturedPrimaryClose
import YM.Integration.WilsonCapturedPrimaryCloseCore
import YM.Integration.WilsonCapturedPrimaryPredictionWindow
import YM.Integration.WilsonReceivedCloseCountertermSlate
import YM.Integration.WilsonReceivedCloseNamedWallet
import YM.Trace.Physicalv2.GermPrices

/-! Read one complete enrolled original pair minus its counterterm on each
date of its close interval, with its original source rent already restored. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySale
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
    (active : Finset V) (width : V → ℝ) (tab δ M : ℝ) (pos : 0 ≤ δ)
    (law : VowsR.LawScroll G φ) (enrolled : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (paid : ∀ x k : ℕ, k ≤ x → ∀ B : ℝ, R.alloy.delay.betaEntry x ≤ B →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ B)
    (fit : ∀ i, m ≤ i → i ≤ b → k ≤ R.alloy.B.a.clock.J i)
    (logDate : (eventually_atTop.mp (WilsonReceivedLogWindow.original R simple D φ paid grades order shelf k seats 0 1 1 zero_le_one)).choose ≤ m)
    (invoiceDate : (eventually_atTop.mp (WilsonCapturedPrimaryReporter.panel R simple frame A (grade target d 1) 0 1 (by decide))).choose ≤ m)
    (ha : a∈active) (hb : a'∈active) (hc : c∈active)
    (heard : WilsonReceivedCloseCountertermSlate.Heard R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source initial top 0 1 1 active width tab (δ*(g b)^grade target d 1))
    (sold : WilsonReceivedCloseNamedWallet.Sold R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source initial active M)
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
          (3*δ*3^high + w*(WilsonCapturedPrimaryPredictionPanel.fee frame N' *
            (4*M^2/((g (i+1))^2*((g (i+1))^2)^d)) + WilsonCapturedPrimaryCoreBill.wrapFee frame A*s₀) + s₀) := by
  have original : WilsonReceivedCloseOrdinaryPurchase.Heard R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source initial top 0 1 1 c s ((3*δ)*(g b)^grade target d 1) := by
    intro i ib mi
    obtain ⟨L,trail,all⟩ := heard i ib mi
    refine ⟨L,trail,?_⟩
    intro x F tag u z B angle window inside U good Y bank program W Z
    have observed := (all x F tag u z window inside good).2 a ha a' hb distinct s pair {c} (by simpa using hc) (fun _ => (1:ℂ))
    have evaluated := observed.2
    norm_num [WilsonReceivedCloseCounterterm.compensated,←mul_assoc] at evaluated
    exact evaluated
  intro i ib mi
  obtain ⟨L,trail,priced⟩ := WilsonCapturedPrimaryCloseCore.original R simple hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats mb source course initial top frame A S target a a' c s distinct pair (3*δ) (mul_nonneg (by norm_num) pos)
    original wrapped calendar late i ib mi
  refine ⟨L,trail,?_⟩
  intro x F tag o Z₀ w κ s₀ budget high rad bank program D' N' y support rank read form rem small represented
  have bill := priced x F tag o Z₀ w κ s₀ support rank read form rem small represented
  have mass := WilsonCapturedPrimaryPredictionWindow.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
    seats i mi (history i ib) simple paid course law enrolled fund (ib.trans_lt top) (fit i mi ib) L (logDate.trans mi)
    frame A high (invoiceDate.trans mi) support o a a' c s distinct pair x F tag
  have pay := (sold i ib mi L trail).2 a ha a' hb c hc
  let σ := min (Poly.toll L.w s) (Poly.toll L.w ((Stock.census V).fire c))
  have equality : σ = min (L.w a*L.w a') (L.w c) := by
    simp [σ,Poly.toll,Census.fire,pair,prod_insert,distinct]
  have wrap : σ⁻¹ ≤ M^2 := by rw [equality];exact pay
  let t := g (i+1)
  have tp : 0<t := inv_pos.mpr (Real.sqrt_pos.mpr (RG02.Actual.coupling_pos R.makes.wilson (ib.trans_lt top)))
  have positive : 0<σ := lt_min (Poly.worth L.salary.positive s) (Poly.worth L.salary.positive _)
  have fee : 0 ≤ WilsonCapturedPrimaryPredictionPanel.fee frame N' := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (sum_nonneg fun _ _ => WilsonCapturedPrimaryPolynomial.price_nonneg ..)
  have units : 4/(σ*t^2)/(t^2)^d ≤ 4*M^2/(t^2*(t^2)^d) := calc
    _ = (4/(t^2*(t^2)^d))*σ⁻¹ := by field_simp
    _ ≤ (4/(t^2*(t^2)^d))*M^2 := mul_le_mul_of_nonneg_left wrap (by positivity)
    _ = _ := by ring
  have gross := mass.trans (mul_le_mul_of_nonneg_left units fee)
  have cert : 0 ≤ WilsonCapturedPrimaryDecoder.invoice frame A N' := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (sum_nonneg fun p _ => WilsonCapturedPrimaryPanel.fee_nonneg A p N')
  have fraction : 0 ≤ 2*(WilsonCapturedPrimaryDecoder.invoice frame A N'*t^target) :=
    mul_nonneg (by norm_num) (mul_nonneg cert (pow_nonneg tp.le _))
  refine bill.trans (mul_le_mul_of_nonneg_left ?_ fraction)
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (add_le_add gross le_rfl) read.nonneg)) le_rfl

end YM.Integration.WilsonCapturedPrimarySale
