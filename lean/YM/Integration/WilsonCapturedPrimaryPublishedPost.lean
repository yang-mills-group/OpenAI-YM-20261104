import YM.Integration.WilsonCapturedPrimaryPublishedOrdinary
import YM.Integration.WilsonCapturedPrimaryPublishedWindow
import YM.Integration.WilsonReceivedLogWindow

/-! The independently published regular ordinary Wilson source and the full
finite Wick moment of the same dated student at the actual physical coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPublishedPost
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    {V : Type} [Fintype V] [DecidableEq V] (grades : V → ℕ)
    (order shelf k slots depth q a : ℕ)
    (deep : 2*(q+1+a+1)+8≤order) (aged : q+1+a+4≤3*k+2) (H cap : ℝ) (hc : 0 ≤ cap) :
    ∀ᶠ i : ℕ in atTop,
    ∀ {m N per : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (_fit : k ≤ R.alloy.B.a.clock.J i) (Q : D.Tab R.rolls)
      (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
      (_course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
      (books : Mentor.Offices.Books D R.rolls Q φ) (law : VowsR.LawScroll G φ)
      (_enrolled : VowsR.Chamber law R.kit D Q books) (_fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
      (hi : m ≤ i) (cut : i < N)
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
        ∀ (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices),
        let issued := Air.craft P.model (fun j => (P.model j).paint x) grades (π (i+1))
          (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let W := Bulk.Fk ((RunFormalChain.fromRun R).step N i per cut) F tag issued angle order
        let U := Integral.sample g angle
        flags (Ψ i).p.threshold U=∅ →
        let student := Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
        let read := (rendered student (Ψ i).p g).log x U
        ∀ s : (Stock.census V).Mode, s.val.card≤a →
          Poly.toll P.w s*‖(Poly.pass read).part s-(Order.value (g:ℂ) (Order.ratio W)).part s‖ ≤
            WilsonReceivedCloseOrdinaryGrade.invoice (Stock.census V) a 0 q 1*g^(q+1) := by
  have each (s : (Stock.census V).Mode) := WilsonCapturedPrimaryPublishedWindow.original R simple D φ width grades s
    (q+1+a) depth order shelf k deep aged H cap hc (zero_lt_one : (0:ℝ)<1)
  filter_upwards [Filter.eventually_all.mpr each,
    WilsonReceivedLogWindow.original R simple D φ width grades order shelf k slots depth H cap hc,
    WilsonReceivedTaylorWindow.potential R simple depth H] with i logs income cool
  intro m N per hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead X _ _ actors pieces physical P x A
    g B b angle z hz eligible F tag issued W U healthy student read s occupied
  have capBill := income hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead actors pieces physical P x A
    z hz eligible F tag
  have gp : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  apply WilsonCapturedPrimaryPublishedOrdinary.original read
    (WilsonCapturedPrimaryPublishedOrdinary.quiet (rendered student (Ψ i).p g) x U) W (Bulk.fk_unit ..) (Bulk.fk_sym ..)
    P.w P.salary.positive g gp (cool N per (by omega) z hz).1 s a q occupied (by omega)
    (fun t _=>(capBill t.val).1)
  intro t _
  have delta := logs t.val hk fit Q π Γ Ψ course books law enrolled fund hi cut P.op P.lesson ahead actors
    P.model P.w P.voter P.cost P.salary x F tag A pieces P.input P.rent P.output P.issued P.affordable z hz eligible healthy
  simpa only [one_mul] using delta

end YM.Integration.WilsonCapturedPrimaryPublishedPost
