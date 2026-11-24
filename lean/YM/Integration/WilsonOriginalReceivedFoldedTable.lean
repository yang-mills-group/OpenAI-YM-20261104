import YM.Integration.WilsonOriginalReceivedFoldedQuiet

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
theorem table {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
    {V : Type} [Fintype V] [DecidableEq V] (grades : V → ℕ)
    (witness : V) (q depth order shelf k slots : ℕ)
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
        Poly.price P.w (read-folded) ≤ (Fintype.card (Stock.census V).Mode : ℝ) * ((8*Ω^slots)*P.rent)+ε*g^q := by
  classical
  let C := Stock.census V
  let T := {s : C.Mode // s.val.Nonempty}
  have pc : 0 < (Fintype.card C.Mode : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (show Nonempty C.Mode from ⟨C.quiet⟩))
  let δ := ε / (Fintype.card C.Mode : ℝ)
  have dp : 0 < δ := div_pos pos pc
  let stage (t : T) := (eventually_atTop.mp (paid R simple D φ width grades
    t.1 t.2.choose t.2.choose_spec q depth order shelf k slots deep aged H cap cap_pos dp)).choose
  filter_upwards [eventually_ge_atTop (Finset.univ.sup stage),
      eventually_ge_atTop (WilsonCoherentMayerRosterWindingRun.firstDate R simple)] with i common opened
  intro m N per hk fit Q π Γ Ψ course books hi cut ahead X _ _ actors pieces physical P x A g B b Ω
    angle z hz inside W clean read teacher writer folded
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have epos : 0 < Ω := zero_lt_one.trans_le P.issued.Waffle.cool
  have each (s : C.Mode) : Poly.toll P.w s * ‖(read-folded).part s‖ ≤ (8*Ω^slots)*P.rent+δ*g^q := by
    by_cases numbered : s.val.Nonempty
    · let t : T := ⟨s,numbered⟩
      have pass : stage t ≤ i := (Finset.le_sup (f:=stage) (Finset.mem_univ t)).trans common
      exact (eventually_atTop.mp (paid R simple D φ width grades t.1 t.2.choose t.2.choose_spec
        q depth order shelf k slots deep aged H cap cap_pos dp)).choose_spec i pass
        hk fit Q π Γ Ψ course books hi cut ahead actors pieces physical P x A z hz inside clean
    · have zero : s=C.quiet := Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp numbered)
      subst s
      have normalized := quiet R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf slots
        physical P x A simple (opened.trans (Nat.le_succ _)) witness clean
      rw [normalized, norm_zero, mul_zero]
      exact add_nonneg (mul_nonneg (by positivity) P.active.le) (mul_nonneg dp.le (pow_nonneg gp.le _))
  have division : (Fintype.card C.Mode : ℝ)*δ=ε := by
    dsimp only [δ]
    field_simp
  calc
    _ ≤ ∑ _s : C.Mode, ((8*Ω^slots)*P.rent+δ*g^q) := Finset.sum_le_sum (fun s _=>each s)
    _ = (Fintype.card C.Mode : ℝ)*((8*Ω^slots)*P.rent+δ*g^q) := by simp [mul_add]
    _ = _ := by rw [mul_add,←mul_assoc (Fintype.card C.Mode : ℝ) δ (g^q),division]

end YM.Integration.WilsonOriginalReceivedFoldedPost
