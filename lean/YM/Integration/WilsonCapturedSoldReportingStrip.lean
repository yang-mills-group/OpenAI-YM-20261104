import YM.Integration.WilsonCapturedStudentPaidRoof
import YM.Integration.WilsonOlderFreshGraphInvoiceOrder

/-! Both ends of the actual source width on precisely the pupil's own posted School figure. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedSoldReportingStrip
open Function Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler AllOrder.Transit.WheelP
open QuadraticLocal.Rebirth QuadraticLocal.Affinity WilsonOriginalReceivedChain Stationary Multi
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open AnalyticBridge VerifiedReset RemainderComparison
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {m N per k i : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (hi : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i hi physical)

local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "coinHat" => R.alloy.B.a.clock.hatBeta i

include P in
theorem original (simple:G.Simple)(gr:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (shown:k≤R.alloy.B.a.clock.J i)(nonzero : 0 < i)(hot:Real.exp 1≤coinHat):
    0<σ ∧ σ⁻¹≤Real.sqrt (Real.log coinHat) ∧
      Real.exp ((min 1 σ)⁻¹^2)≤coinHat ∧ Real.exp (σ/4)≤(16*budgetR R i)^2:=by
  have sp:0<σ:=Poetry.Agenda.stem ..
  have booked:Real.exp (σ⁻¹^2)≤coinHat:=by
    cases i with
    | zero=>omega
    | succ j=>exact gr _ k shown _ ((R.alloy.B.valid.pays j).trans
        (Push.Corrected.Last.band_le R.alloy.B.a simple (Nat.le_succ j)))
  have ph:0<coinHat:=(Real.exp_pos _).trans_le hot
  have window:σ⁻¹^2≤Real.log coinHat:=by
    simpa using Real.log_le_log (Real.exp_pos _) booked
  obtain ⟨_,_,room,_,_,ax,good,_⟩:=P.issued.Waffle.soon
  have price:=WilsonOlderFreshGraphInvoiceOrder.escape G (Ψ i).p room ax good (fig).cap (fig).count
  have quote:=P.issued.Waffle.quote.trans P.issued.Beamwork
  have step:Real.exp (σ/4/2)≤16*budgetR R i:=
    price.trans (mul_le_mul_of_nonneg_left quote (by norm_num))
  refine ⟨sp,Real.le_sqrt_of_sq_le window,?_,?_⟩
  · rcases le_total 1 σ with h|h
    · simpa only [min_eq_left h,inv_one,one_pow] using hot
    · simpa only [min_eq_right h] using booked
  · calc
      Real.exp (σ/4)=(Real.exp (σ/4/2))^2:=by rw [← Real.exp_nat_mul];congr 1;push_cast;ring
      _≤_:=pow_le_pow_left₀ (Real.exp_pos _).le step _

end YM.Integration.WilsonCapturedSoldReportingStrip
