import YM.Integration.WilsonCapturedCoveredSourceWage
import YM.Integration.WilsonOriginalReceivedCopiedCover

/-! The actual student on the selected original post, with its course's lower
layout, source radii, charged link chart and earned support reserve. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedStudentAngularWage
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

theorem stipend_le : (stipend) ≤ 1:=by
  have cost:=Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  have pos:=P.issued.Waffle.paysAbove
  calc
    _ ≤ (Ω)*P.cost:=mul_le_mul_of_nonneg_right P.issued.Waffle.earns cost
    _ ≤ (Ω)*(Ω)⁻¹:=mul_le_mul_of_nonneg_left P.affordable pos.le
    _ = 1:=mul_inv_cancel₀ pos.ne'

theorem price {grid:Side} (h:(R.family.side i per).val ∣ grid.val)
    (cut: _ → Prop) (t:Wallet actors) (s:(J).Mode) (v:s.val) (b:Fin (Pages (R.family.side i per) grid))
    (j d r:ℕ) :
    let home:=(page h ((P.passport.coarser (op).ratio).origin v.val) b).val
    Poly.toll P.w s * exposure (σ/8) r home (field h (stud) t s v cut j d b) ≤
      fare G d r σ 1:=by
  intro home
  have seed:=Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
  have paid:=WilsonCapturedCoveredSourceWage.original h (stud) t s v P.issued.earning
    seed cut j d r b
  apply paid.trans
  have z:0≤UVNext.PricedKernels.basin (σ/4):=by
    unfold UVNext.PricedKernels.basin;apply mul_nonneg (by norm_num);apply tsum_nonneg;intro n;unfold Next.Scheduling.decay;positivity
  unfold WilsonCapturedCoveredSourceWage.fare
  gcongr
  · exact WilsonOriginalSuspendedTensor.nonnegative G seed d
  · exact stipend_le R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats hi physical P

theorem byDate {grid:Side} (h:(R.family.side i per).val ∣ grid.val)
    (cut: _ → Prop) (t:Wallet actors) (s:Hot (J)) (v:s.val.val) (b:Fin (Pages (R.family.side i per) grid))
    (e r:ℕ) :
    let M:=crop (stud) cut
    let tape:=AllOrder.Floe.Step.tape (Burn.horizon k+2)
    let Z:=WilsonOriginalPinnedGradedPeek.bank h M t grades (π (i+1)) tape
    let home:=(page h ((P.passport.coarser (op).ratio).origin v.val) b).val
    Poly.toll P.w s.val * exposure (σ/8) r home (field h (stud) t s.val v cut 0 (Z.power s+e) b)
      ≤ fare G (Z.power s+e) r σ 1 ∧
    ∀(base:Site grid)(A:Link G grid),
      WilsonCapturedRootedAngularSlots.thermal
        (WilsonOriginalPolarizedAngularPage.board h base (WilsonOriginalJointDeckMotion.motion G)
          (WilsonOriginalPinnedDeckOrbit.needle h M t s.val v 0 b)) (Z.power s+e) A =
        (peek h M grades (π (i+1)) tape t e A).part s.val:=by
  intro M tape Z home
  refine ⟨price R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats hi physical P h cut t s.val v b 0 _ r,?_⟩
  exact fun base A=>boundToProgram h (stud) t P.issued.earning (Poetry.Agenda.stem ..) cut s v
    (π (i+1)) tape b base e A
end YM.Integration.WilsonCapturedStudentAngularWage
