import YM.Integration.WilsonReceivedTaylorWindow
import YM.Integration.WilsonReceivedInheritedFee
import YM.Integration.WilsonOriginalAxialWinding

/-! Signed finite-program comparison for every genuinely returned original block,
with a cofinal date fixed before ultraviolet cutoff, period, sites, and source tests. -/

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedPaidCourse
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (paid : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
    {V : Type} [Fintype V] [DecidableEq V] {marks : Census V} (grades : V → ℕ)
    (s : marks.Mode) (v : V) (hv : v ∈ s.val) (q depth order shelf k slots : ℕ) (deep : 2*(q+1)+8 ≤ order)
    (aged : q+4 ≤ 3*k+2) (H cap : ℝ)
    (cap_pos : 0 ≤ cap) {ε : ℝ} (pos : 0 < ε) :
    ∀ᶠ i : ℕ in atTop,
    ∀ {m N per : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (_fit : k ≤ R.alloy.B.a.clock.J i) (Q : D.Tab R.rolls)
      (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
      (_course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
      (books : Mentor.Offices.Books D R.rolls Q φ) (law : VowsR.LawScroll G φ)
      (_enrolled : VowsR.Chamber law R.kit D Q books) (_fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
      (hi : m ≤ i) (cut : i < N)
      (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
      (_capCount : op.count=slots) (lesson : Lesson (N:=N) R hk D Q π Γ hi)
      (ahead : Mentor.Forecast D R.rolls Q φ books)
      {ι : Type} {X : V → Type} [∀ u, AddCommGroup (X u)] [∀ u, Module ℝ (X u)]
      {passport : Earn.Passport (R.family.side (i+1) per) V}
      (actors : ∀ u, Set (X u)) (M : ι → Row passport marks G (Affinity.Wallet actors))
      (w : V → ℝ)
      (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
        order op.count op.stage k (R.alloy.B.a.clock.J i)) (cost : ℝ)
      (_incoming : Scene.Armada M w grades (Poetry.Agenda.seed D φ (Burn.horizon k)
        (R.alloy.B.a.clock.J (i+1))) cost order op.count shelf)
      (x : Affinity.Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
      (tag : (R.family.path.levels.clock.op i per).Choices) (A : Stationary.Link G (R.family.side i per))
      {old next : Type} (pieces : ∀ u, Submodule ℝ (X u))
      (Z : Tint.Incoming passport (Ψ (i+1)) (Affinity.Wallet actors) old marks)
      (rent : ℝ) (Y : Tint.Incoming (passport.coarser (R.family.path.levels.clock.op i per).ratio)
        (Ψ i) (Affinity.Wallet actors) next marks)
      (_returned : Oak.Buffered.SuccessStory R hk D Q π Γ Ψ books hi op lesson ahead
        actors pieces M Z w grades order shelf voter rent cost Y)
      (_entrance : cost ≤ (Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf)⁻¹),
      let g := Coat.gStep (R.family.path.rep N per (i+1)).beta
      let B := R.family.path.levels.budget i
      let b := R.family.path.levels.clock.hatBeta i
      let Ω := Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
      let angle := Stationary.arm G (R.family.side i per) 1 A
      ∀ z : ℝ, |z| ≤ |H| * (Real.log b)^depth*((B.B:ℝ)^2*B.threshold)/g →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap*|z|) →
        let W := Integral.sample g angle
        flags (Ψ i).p.threshold W=∅ →
        let read := Order.logTo (Fintype.card V) ((((Ψ i).eval W:ℂ)⁻¹) •
           LocalComparison.actualPush R.family N per i ((Tint.Patrol.picture M Z).density x) W)
        let issued := Air.craft M (fun a => (M a).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let step := (RunFormalChain.fromRun R).step N i per cut
        let point := Order.value (g:ℂ) (Order.logMarked (Bulk.Fk step F tag issued angle order))
        Poly.toll w s*‖(read-point).part s‖ ≤ (8*Ω^op.count)*rent+ε*g^q := by
  let δ := ε/3
  have dp : 0 < δ := div_pos pos (by norm_num)
  let opening := WilsonFirstReceivedEarnedFee.opening R simple slots q order k deep aged dp
  filter_upwards [WilsonReceivedTaylorWindow.funded R simple D φ paid order shelf depth (Fintype.card V) cap H cap_pos dp,
      WilsonReceivedTaylorWindow.potential R simple depth H,
      WilsonOriginalAxialWinding.eventually_open R simple 1 (2*cap) δ 0 0 q 1,
      eventually_ge_atTop (WilsonCoherentMayerRosterWindingRun.firstDate R simple),
      eventually_ge_atTop opening] with i Taylor window seam first late
  intro m N per hk fit Q π Γ Ψ course books law enrolled fund hi cut op capCount lesson ahead ι X _ _ passport
    actors M w voter cost incoming x F tag A old next pieces Z rent Y returned entrance g B b Ω angle z hz inside W clean read issued step point
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  obtain ⟨cool,top⟩ := window N per cut z hz
  have rich : 1 ≤ Ω := by linarith only [returned.Waffle.strong]
  have opct : 0 < Ω := zero_lt_one.trans_le rich
  have small : cost ≤ 1 := entrance.trans ((inv_le_one₀ opct).2 rich)
  have nonnegative : 0 ≤ cost := Push.AbsoluteSums.budget_nonneg (incoming.suggests 0)
  let P₁ := passport.coarser (R.family.path.levels.clock.op i per).ratio
  let σ := Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
  let capFee := (Oak.figureReal R hk D Q π Γ books hi op lesson ahead order shelf).produce
     (R.family.path.levels.clock.op i per).ratio.count*cost
  let P := WilsonReceivedSourceRoster.tariff G σ (cap*|z|) g order shelf
  have cf : capFee ≤ 1 := calc
    _ ≤ Ω*cost := mul_le_mul_of_nonneg_right returned.Waffle.earns nonnegative
    _ ≤ Ω*Ω⁻¹ := mul_le_mul_of_nonneg_left entrance opct.le
    _ = 1 := mul_inv_cancel₀ opct.ne'
  have seats : (s.val.image P₁.origin).card ≤ Fintype.card V :=
    Finset.card_image_le.trans (Finset.card_le_univ s.val)
  have signed : 0 ≤ P := by dsimp [P,WilsonReceivedSourceRoster.tariff]; positivity
  have taylorPay : P*((s.val.image P₁.origin).card*capFee) ≤ δ*g^q := calc
    _ ≤ P*(Fintype.card V) := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left cf (Nat.cast_nonneg _)).trans (by simpa only [mul_one] using (Nat.cast_le.mpr seats : ((s.val.image P₁.origin).card:ℝ) ≤ Fintype.card V))) signed
    _ ≤ δ*g^order := Taylor N per cut k fit z hz
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le cool (by omega)) dp.le
  let upper := R.alloy.B.a.clock.hatBeta (i+1)
  have axis (e) : ‖Exterior.collect G angle e‖ ≤ 2*cap*upper^1 := calc
    _ ≤ cap*|z| := inside e
    _ ≤ cap*(2*upper) := mul_le_mul_of_nonneg_left top cap_pos
    _ = _ := by ring
  have wind := WilsonOriginalAxialWinding.measured R hk D Q π Γ law books enrolled fund hi cut op lesson
    cost nonnegative small A 1 (2*cap) δ 1 0 0 q 1 0 le_rfl (by positivity) dp
    (seam i le_rfl) zero_le_one (by simp) (by omega) axis
  simp only [pow_zero,mul_one] at wind
  have old := WilsonReceivedInheritedFee.original R hk D Q π Γ Ψ books hi cut op lesson ahead actors M w grades order shelf voter cost
    pieces Z rent Y returned simple q deep aged dp (by simpa only [capCount] using late)
  have whole := WilsonReceivedPhysicalFinite.original R hk D Q π Γ Ψ course books hi cut op lesson ahead
    actors M w grades order shelf voter cost incoming x F tag A pieces Z rent Y returned small simple (first.trans (Nat.le_succ _))
    (mul_nonneg cap_pos (abs_nonneg z)) inside clean s v hv
  refine whole.trans ((add_le_add (add_le_add old taylorPay) wind).trans_eq ?_)
  dsimp only [δ]
  ring

end YM.Integration.WilsonReceivedPaidCourse
