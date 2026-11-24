import YM.Integration.WilsonReceivedSourceCoefficientIncome
import YM.Integration.WilsonOriginalReceivedFoldedPost

/-! The outgoing signed coefficient at a z in its measured axial window, before choosing N or period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedSourceCoefficientWindow
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

/-- The paid angular cutoff permits any fixed power of the weighted true coefficient with one g
to spare. The stage is the same for all physical regulators, posts, sources, faces and orders j. -/
theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    {V : Type} [Fintype V] [DecidableEq V] (grades : V → ℕ)
    (order shelf k slots depth power : ℕ) (H cap : ℝ) (hc : 0 ≤ cap) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ i : ℕ in atTop,
    ∀ {m N per : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (_fit : k ≤ R.alloy.B.a.clock.J i) (Q : D.Tab R.rolls)
      (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
      (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (_cut : i < N)
      (ahead : Mentor.Forecast D R.rolls Q φ books) {X : V → Type}
      [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
      (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v))
      (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
      (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
        order shelf slots i hi physical) (x : Wallet actors) (A : Stationary.Link G (R.family.side i per)),
      let g := Coat.gStep (R.family.path.rep N per (i+1)).beta
      let B := R.family.path.levels.budget i
      let b := R.family.path.levels.clock.hatBeta i
      let angle := Stationary.arm G (R.family.side i per) 1 A
      ∀ z : ℝ, |z| ≤ |H| * (Real.log b)^depth*((B.B:ℝ)^2*B.threshold)/g →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap*|z|) →
        let student := Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
          P.model order P.voter
        let writer := Air.craft student (fun a => (student a).paint x) grades (π i)
          (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        ∀ j : ℕ, j ≤ order → ∀ s : (Stock.census V).Mode,
          g*(Poly.toll P.w s * ‖(Air.discharge writer j angle).part s‖)^power ≤ ε := by
  let d := (order+shelf+1)*power
  filter_upwards [WilsonReceivedTaylorWindow.funded R simple D φ width 0 d depth
    ((Fintype.card V)^power) cap H hc ep] with i window
  intro m N per hk fit Q π Γ Ψ books hi cut ahead X _ _ actors pieces physical P x A g B b angle
      z hz axis student writer j hj s
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  let Ω := Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
  let capital := (Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf).produce
    (R.family.path.levels.clock.op i per).ratio.count*P.cost
  have positive : 0 < Ω := zero_lt_one.trans_le P.issued.Waffle.cool
  have cost₀ : 0 ≤ P.cost := Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  have cheap : capital ≤ 1 := calc
    _ ≤ Ω*P.cost := mul_le_mul_of_nonneg_right P.issued.Waffle.earns cost₀
    _ ≤ Ω*Ω⁻¹ := mul_le_mul_of_nonneg_left P.affordable positive.le
    _ = 1 := mul_inv_cancel₀ positive.ne'
  let σ := Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
  let a := max 1 (2*(G.colorScale*(cap*|z|))/σ)
  have one : 1 ≤ a := le_max_left _ _
  have a₀ : 0 ≤ a := zero_le_one.trans one
  have paid : a^(d+2)*g*((Fintype.card V:ℝ)^power) ≤ ε := by
    simpa only [WilsonReceivedSourceRoster.tariff,Nat.zero_add,Nat.cast_pow,pow_one,pow_zero,mul_one,
      a,σ,g,d,Pert.Asymptotics.regulatorRun,Coat.gStep] using window N per (Nat.succ_le_of_lt cut) k fit z hz
  have cap₀ := mul_nonneg hc (abs_nonneg z)
  have actual := WilsonReceivedSourceCoefficientIncome.original student P.w grades P.issued.earning
    (Poetry.Agenda.stem ..) x A cap₀ axis j hj (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) s
  let dest := P.passport.coarser (R.family.path.levels.clock.op i per).ratio
  have count : (s.val.image dest.origin).card ≤ Fintype.card V :=
    Finset.card_image_le.trans (Finset.card_le_univ _)
  have expense : ((s.val.image dest.origin).card:ℝ)*capital ≤ (Fintype.card V:ℝ) :=
    (mul_le_of_le_one_right (Nat.cast_nonneg _) cheap).trans (by exact_mod_cast count)
  have bound : Poly.toll P.w s * ‖(Air.discharge writer j angle).part s‖ ≤
      a^(order+shelf+1) * (Fintype.card V:ℝ) :=
    actual.trans (mul_le_mul_of_nonneg_left expense (pow_nonneg a₀ _))
  have non := mul_nonneg (Poly.worth P.issued.earning.positive s).le
    (norm_nonneg ((Air.discharge writer j angle).part s))
  calc
    _ ≤ g*(a^(order+shelf+1)*(Fintype.card V:ℝ))^power :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ non bound _) gp.le
    _ = a^d*g*((Fintype.card V:ℝ)^power) := by rw [mul_pow,←pow_mul]; dsimp only [d]; ring
    _ ≤ a^(d+2)*g*((Fintype.card V:ℝ)^power) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one (by omega)) gp.le) (by positivity)
    _ ≤ _ := paid

end YM.Integration.WilsonReceivedSourceCoefficientWindow
