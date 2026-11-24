import YM.Integration.WilsonOriginalReceivedFoldedPost

/-! The paid signed Wilson-to-cover estimate on any actual received post. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedFoldedPost
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

/-- The cofinal date precedes all physical regulators and the choice of the actual
funded post. Its inherited regular residual is charged in the original source radius. -/
theorem paid {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
    {V : Type} [Fintype V] [DecidableEq V] (grades : V → ℕ)
    (s : (Stock.census V).Mode) (v : V) (hv : v∈s.val) (q depth order shelf k slots : ℕ)
    (deep : 2*(q+1)+8 ≤ order) (aged : q+4 ≤ 3*k+2) (H cap : ℝ)
    (cap_pos : 0 ≤ cap) {ε : ℝ} (pos : 0 < ε) :
    ∀ᶠ i : ℕ in atTop,
    ∀ {m N per : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (_fit : k ≤ R.alloy.B.a.clock.J i) (Q : D.Tab R.rolls)
      (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
      (_course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
      (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (_cut : i < N)
      (ahead : Mentor.Forecast D R.rolls Q φ books) {X : V → Type}
      [∀ u, AddCommGroup (X u)] [∀ u, Module ℝ (X u)]
      (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v))
      (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
      (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
        order shelf slots i hi physical) (x : Wallet actors)
      (A : Stationary.Link G (R.family.side i per)),
      let g := Coat.gStep (R.family.path.rep N per (i+1)).beta
      let B := R.family.path.levels.budget i
      let b := R.family.path.levels.clock.hatBeta i
      let Ω := Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
      let angle := Stationary.arm G (R.family.side i per) 1 A
      ∀ z : ℝ, |z| ≤ |H| * (Real.log b)^depth*((B.B:ℝ)^2*B.threshold)/g →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap * |z|) →
        let W := Integral.sample g angle
        flags (Ψ i).p.threshold W=∅ →
        let read := Order.logTo (Fintype.card V) ((((Ψ i).eval W:ℂ)⁻¹) •
          LocalComparison.actualPush R.family N per i (physical x) W)
        let teacher := Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
        let writer := Air.craft teacher (fun a=>(teacher a).paint x) grades (π i)
          (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let folded := WilsonCoherentMayerWindingGrades.panel order (g:ℂ) (fun d=>Air.discharge writer d angle)
        Poly.toll P.w s * ‖(read-folded).part s‖ ≤ (8*Ω^slots)*P.rent+ε*g^q := by
  let δ := ε/2
  have dp : 0 < δ := half_pos pos
  let firstFee := WilsonFirstReceivedEarnedFee.opening R simple slots q order k deep aged dp
  filter_upwards [WilsonReceivedTaylorWindow.funded R simple D φ width order shelf depth (Fintype.card V) cap H cap_pos dp,
      WilsonReceivedTaylorWindow.potential R simple depth H,
      eventually_ge_atTop (WilsonCoherentMayerRosterWindingRun.firstDate R simple),
      eventually_ge_atTop firstFee] with i Taylor window first late
  intro m N per hk fit Q π Γ Ψ course books hi cut ahead X _ _ actors pieces physical P x A g B b Ω
    angle z hz inside W clean read teacher writer folded
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have cool := (window N per cut z hz).1
  have rich : 1 ≤ Ω := P.issued.Waffle.cool
  have opct : 0 < Ω := zero_lt_one.trans_le rich
  have nn : 0 ≤ P.cost := Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  let dest := P.passport.coarser (R.family.path.levels.clock.op i per).ratio
  let σ := Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
  let capital := (Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf).produce
    (R.family.path.levels.clock.op i per).ratio.count*P.cost
  let tariff := WilsonReceivedSourceRoster.tariff G σ (cap * |z|) g order shelf
  have cheap : capital ≤ 1 := calc
    _ ≤ Ω*P.cost := mul_le_mul_of_nonneg_right P.issued.Waffle.earns nn
    _ ≤ Ω*Ω⁻¹ := mul_le_mul_of_nonneg_left P.affordable opct.le
    _ = 1 := mul_inv_cancel₀ opct.ne'
  have count : (s.val.image dest.origin).card ≤ Fintype.card V := Finset.card_image_le.trans (Finset.card_le_univ _)
  have positive : 0 ≤ tariff := by dsimp [tariff, WilsonReceivedSourceRoster.tariff]; positivity
  have tail : tariff*((s.val.image dest.origin).card*capital) ≤ δ*g^q := calc
    _ ≤ tariff*(Fintype.card V) := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left cheap (Nat.cast_nonneg _)).trans
        (by simpa only [mul_one] using (Nat.cast_le.mpr count : ((s.val.image dest.origin).card:ℝ) ≤ Fintype.card V))) positive
    _ ≤ δ*g^order := Taylor N per cut k fit z hz
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le cool (by omega)) dp.le
  have earned := WilsonReceivedInheritedFee.original R hk D Q π Γ Ψ books hi cut P.op P.lesson ahead actors
    P.model P.w grades order shelf P.voter P.cost pieces P.input P.rent P.output P.issued simple
    q deep aged dp (by simpa only [P.capacity] using late)
  have signed := measured R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf slots
    physical P x A simple (first.trans (Nat.le_succ _)) (mul_nonneg cap_pos (abs_nonneg z)) inside clean s v hv
  refine signed.trans ((add_le_add earned tail).trans_eq ?_)
  rw [P.capacity]
  dsimp only [δ]
  ring

end YM.Integration.WilsonOriginalReceivedFoldedPost
