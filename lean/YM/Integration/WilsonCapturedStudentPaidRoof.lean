import YM.Integration.WilsonCapturedStudentAngularWage
import YM.Integration.WilsonCapturedSourceAngularRoof
import YM.Integration.WilsonThermometerUnitFilingTuition
import YM.Integration.WilsonPhysicalHistoryPriorAperture

/-! Receive the original prior strip on its same preselected hierarchy.
The source cost is paid before the ultraviolet cutoff and physical period. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedStudentPaidRoof
open Function Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler AllOrder.Transit.WheelP
open QuadraticLocal.Rebirth QuadraticLocal.Affinity WilsonOriginalReceivedChain Stationary Multi
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonCapturedCoveredSourceWage WilsonOriginalSuspendedTensor
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

local notation "stud" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "op" => R.family.path.levels.clock.op i per
local notation "stipend" => (fig).produce (op).ratio.count*P.cost
local notation "J" => Stock.census V


theorem original (simple:G.Simple) (grant:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (mi:0 < i) (fit:k ≤ R.alloy.B.a.clock.J i) {δ:ℝ}(δp:0<δ) (d r:ℕ) {grid:Side}
    (h:(R.family.side i per).val ∣ grid.val) (cut: _ → Prop) (t:Wallet actors)
    (s:(J).Mode) (v:s.val) (b:Fin (Pages (R.family.side i per) grid))(j:ℕ) :
    let μ:=min 1 σ
    let β:=max (Real.exp 1) (R.alloy.B.a.clock.hatBeta i)
    let home:=(page h ((P.passport.coarser (op).ratio).origin v.val) b).val
    Poly.toll P.w s * exposure (μ/8) r home (field h (stud) t s v cut j d b) ≤
      WilsonCapturedSourceAngularRoof.roof G d r δ*β^δ:=by
  intro μ β home
  have pos:=Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
  have mp:0<μ:=lt_min one_pos pos
  have thin:=WilsonThermometerUnitFilingTuition.narrow (stud) P.issued.earning (min_le_right 1 σ)
  have priced:=WilsonCapturedCoveredSourceWage.original h (stud) t s v thin mp cut j d r b
  have spends: (stipend) ≤ 1:=WilsonCapturedStudentAngularWage.stipend_le R hk D Q π Γ Ψ
    books ahead actors pieces grades order shelf seats hi physical P
  have roof:WilsonCapturedCoveredSourceWage.fare G d r μ (stipend) ≤ WilsonCapturedCoveredSourceWage.fare G d r μ 1:=by
    have amount:0≤UVNext.PricedKernels.basin (μ/4):=by
      unfold UVNext.PricedKernels.basin;apply mul_nonneg (by norm_num);apply tsum_nonneg;intro n;unfold Next.Scheduling.decay;positivity
    unfold WilsonCapturedCoveredSourceWage.fare
    gcongr
    exact WilsonOriginalSuspendedTensor.nonnegative G mp d
  have actual : Real.exp ((σ)⁻¹^2) ≤ R.alloy.B.a.clock.hatBeta i := by
    cases i with
    | zero => omega
    | succ l => exact grant _ k fit _ ((R.alloy.B.valid.pays l).trans (Push.Corrected.Last.band_le R.alloy.B.a simple (Nat.le_succ l)))
  have booked:Real.exp (μ⁻¹^2) ≤ β:=by
    by_cases clear:σ≤1
    · exact (show Real.exp (μ⁻¹^2) ≤ R.alloy.B.a.clock.hatBeta i by simpa only [μ,min_eq_right clear] using actual).trans (le_max_right ..)
    · simpa only [μ,min_eq_left (le_of_not_ge clear),inv_one,one_pow] using (le_max_left (Real.exp 1) (R.alloy.B.a.clock.hatBeta i))
  exact priced.trans (roof.trans (WilsonCapturedSourceAngularRoof.original G d r mp (min_le_left ..) δp booked))

end YM.Integration.WilsonCapturedStudentPaidRoof
