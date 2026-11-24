import YM.Integration.WilsonCoveredOrdinaryHeldFee

/-! On an already specified paid post, the finite-to-cover ordinary price for all signed entries
uses the genuine emitted log and the same course. No selection or rent adjustment is made. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoveredOrdinarySpecificPost
open WilsonIndependentOrdinaryPairGrade
open Filter Finset Multi Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

section Grading
theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    {V : Type} [Fintype V] [DecidableEq V] (grades : V → ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    (order shelf k slots depth a v w q : ℕ) (H cap C : ℝ) (hc : 0 ≤ cap) {ε : ℝ} (ep:0<ε) :
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
        let student := Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
        let writer := Air.craft student (fun s=>(student s).paint x) grades (π i)
          (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let K := fun l => Air.discharge writer l angle

        (∀lag,lag ≤ order → ∀s:(Stock.census V).Mode,
          Poly.toll P.w s*‖(Order.observe _ order (Order.logMarked W) lag).part s-(K lag).part s‖ ≤
            (WilsonCoveredOrdinaryHeldFee.factor (Stock.census V) a C ε/((order:ℝ)+1))*g^(q+w+v+a)) ∧
        ∀ (rows:Finset (Stock.census V).Mode) (c:(Stock.census V).Mode→ℂ),
          (∀s∈rows,s.val.card ≤ a ∧ g^v ≤ Poly.toll P.w s) →
          g^w*(∑s ∈ rows,‖c s‖) ≤ C →
          ‖(∑s ∈ rows,c s*(Order.value (g:ℂ) (Order.ratio W)).part s)
            -(∑s ∈ rows,c s*WilsonCoveredOrdinaryPolynomial.evaluated order K (g:ℂ) s)‖ ≤ ε*g^q := by
  let η:=WilsonCoveredOrdinaryHeldFee.factor (Stock.census V) a C ε
  have hp:0<η:=WilsonCoveredOrdinaryHeldFee.positive _ _ _ ep
  filter_upwards [WilsonCoveredOrdinaryWindingPost.original R simple D φ grades order shelf k slots depth (q+w+v+a)
      H cap hc hp, WilsonReceivedLogWindow.original R simple D φ width grades order shelf k slots depth H cap hc,
    WilsonReceivedTaylorWindow.potential R simple depth H] with i close charges window
  intro m N per hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead X _ _ actors pieces physical P x A
    g B b angle z hz inside F tag issued W student writer K
  have wind:=close hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead actors pieces physical P x A z hz inside F tag
  have masses:=charges hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead actors pieces physical P x A z hz inside F tag
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have cold:=(window N per (Nat.succ_le_of_lt cut) z hz).1
  refine ⟨wind.1,?_⟩
  intro rows c paid invoice
  exact WilsonCoveredOrdinaryHeldFee.signed _ a v w q ep gp cold rows (Poly.toll P.w)
    (fun s=>(Order.value (g:ℂ) (Order.ratio W)).part s)
    (WilsonCoveredOrdinaryPolynomial.evaluated order K (g:ℂ)) c paid
    (fun s _=>wind.2 s (fun d _=>(masses d.val).1)) invoice

end Grading
end YM.Integration.WilsonCoveredOrdinarySpecificPost
