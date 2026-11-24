import YM.Integration.WilsonOriginalCoveredHearing

/-! Measured signed original integral compared with the independent covered recursion on every reached date. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCoveredSignedReceipt
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

/-- The cofinal date precedes all physical regulators and the choice of the actual
funded post. Its inherited regular residual is charged in the original source radius. -/
theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
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
      {b : ℕ} (mb : m ≤ b) (inlet : b<N)
      (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))
      (home : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
        order shelf slots b mb source)
      (top : WilsonOriginalCopiedHistory.Values G (Stock.census V) (R.family.side b per))
      (_pass : Pass D Q R.alloy R.kit) (_month : QuadraticLocal.Rebirth.Scholar.Month R.rolls D Q R.alloy.delay)
      (_fits : order≤Burn.horizon k+1) (_shelved : shelf≤R.alloy.B.a.clock.J m)
      (_entry : ∀ (grid : Side) (div : (R.family.side b per).val∣grid.val) (d : ℕ), d≤order → ∀ y,
        top grid div d y=FVA1Physical.TwoReset.peek div
          (Oak.student (n:=per) R hk D Q π Γ books mb home.op home.lesson ahead actors home.model order home.voter)
          grades (π (b+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) x d y)
      (_trail : WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf
        slots mb source home i hi physical P), ∃ ib : i≤b, ∀ (A : Stationary.Link G (R.family.side i per)),
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
        let formal := WilsonOriginalCoveredEvolution.run R inlet π Γ (Burn.horizon k+2) order grades top
        let target := WilsonCoherentMayerWindingGrades.panel order (g:ℂ)
          (fun d=>formal i ib _ (dvd_refl _) d A)
        Poly.price P.w (read-target) ≤ (Fintype.card (Stock.census V).Mode : ℝ) * ((8*Ω^slots)*P.rent)+ε*g^q := by
  classical
  filter_upwards [WilsonOriginalReceivedFoldedPost.table R simple D φ width grades witness q depth
    order shelf k slots deep aged H cap cap_pos pos] with i issued
  intro m N per hk fit Q π Γ Ψ course books floor cut ahead X _ _ actors pieces physical P x b mb inlet
    source home top pass month fits shelved entry trail
  obtain ⟨ib, invoice⟩ := WilsonOriginalCoveredHearing.evaluated R hk D Q π Γ Ψ books ahead actors
    pieces grades order shelf slots mb source home x top inlet course pass month fits shelved entry trail
  refine ⟨ib, ?_⟩
  intro A g B β Ω angle z hz bounded W healthy read formal target
  have paid := issued hk fit Q π Γ Ψ course books floor cut ahead actors pieces physical P x A
    z hz bounded healthy
  change Poly.price P.w (read-target) ≤ _ 
  change Poly.price P.w (read-_) ≤ _ at paid
  exact (congrArg (fun v : Poly (Stock.census V)=>Poly.price P.w (read-v)) (invoice (g:ℂ) A)).le.trans paid

end YM.Integration.WilsonOriginalCoveredSignedReceipt
