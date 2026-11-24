import YM.Integration.WilsonReceivedRestoredOrdinaryCost
import YM.Integration.WilsonReceivedCloseSourceCalendar
import YM.Integration.WilsonReceivedOwnOrdinaryPanel
import YM.Integration.WilsonCoveredOrdinarySpecificPost

/-! On any one retained close-window post, the same original normalized all-field
source has both its signed finite and folded ordinary coefficients at every paid face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChargedOrdinaryReturn
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
    (order shelf k slots depth a v q : ℕ)
    (deep : 2*((q+1+v+a)+1)+8 ≤ order) (aged : (q+1+v+a)+4 ≤ 3*k+2) (H cap : ℝ) (hc : 0 ≤ cap) {ε : ℝ} (ep:0<ε) :
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
      let Ω:=Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
      (8*Ω^P.op.count)*P.rent ≤ (1/2)*g^(q+1+v+a) →
      ∀ z : ℝ, |z| ≤ |H| * (Real.log b)^depth*((B.B:ℝ)^2*B.threshold)/g →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap*|z|) →
        let U:=Integral.sample g angle
        flags (Ψ i).p.threshold U = ∅ →
        ∀ (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices),
        let issued := Air.craft P.model (fun j => (P.model j).paint x) grades (π (i+1))
          (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let W := Bulk.Fk ((RunFormalChain.fromRun R).step N i per cut) F tag issued angle order
        let student := Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
        let writer := Air.craft student (fun s=>(student s).paint x) grades (π i)
          (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let K := fun l => Air.discharge writer l angle

        let Y:=(((Ψ i).eval U:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i (physical x) U
        ∀s:(Stock.census V).Mode, s.val.card ≤ a → g^v ≤ Poly.toll P.w s →
          ‖Y.part s-(Order.value (g:ℂ) (Order.ratio W)).part s‖ ≤ (ε/2)*g^q ∧
          ‖Y.part s-WilsonCoveredOrdinaryPolynomial.evaluated order K (g:ℂ) s‖ ≤ ε*g^q := by
  let p:=q+1+v+a
  let fee:=WilsonReceivedRestoredOrdinaryCost.fee (Stock.census V) a
  have feePaid:=eventually_atTop.mp (WilsonReceivedCloseSourceCalendar.reporter_fee R simple
    (WilsonReceivedRestoredOrdinaryCost.nonneg (Stock.census V) a) (half_pos ep))
  filter_upwards [WilsonReceivedOwnOrdinaryPanel.original R simple D φ width grades p depth order shelf k slots
      deep aged H cap hc (ε:=1/2) (by norm_num),
    WilsonCoveredOrdinarySpecificPost.original R simple D φ grades width order shelf k slots depth a v 0 q
      H cap 1 hc (half_pos ep),WilsonReceivedTaylorWindow.potential R simple depth H,
    eventually_ge_atTop feePaid.choose] with i physicalGrade winding window late
  intro m N per hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead X _ _ actors pieces physical P x A
    g B b angle Ω rent z hz inside U healthy F tag issued W student writer K Y s live wage
  let E:=(8*Ω^P.op.count)*P.rent+(1/2)*g^p
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have cold:=(window N per (Nat.succ_le_of_lt cut) z hz).1
  have omegaPay:0≤Ω:=(by norm_num:(0:ℝ)≤4).trans P.issued.Waffle.strong
  have en:0≤E:=add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg omegaPay _)) P.active.le)
    (mul_nonneg (by norm_num) (pow_nonneg gp.le _))
  have small:E≤g^p:=by dsimp only [E,p];linarith only [rent]
  have full:=physicalGrade hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead actors pieces physical
    P x A z hz inside healthy F tag s (q+1+v) (by omega)
  have cost:=WilsonReceivedRestoredOrdinaryCost.original (Stock.census V) s a v q gp cold live wage
    (norm_nonneg _) en small full
  have money : fee*g ≤ ε/2 := feePaid.choose_spec (i+1) (Nat.le_succ_of_le late) N per (Nat.succ_le_of_lt cut)
  have fine: ‖Y.part s-(Order.value (g:ℂ) (Order.ratio W)).part s‖ ≤ (ε/2)*g^q := calc
    _ ≤ fee*g^(q+1) := cost
    _ = (fee*g)*g^q := by rw [pow_succ];ring
    _ ≤ _ := mul_le_mul_of_nonneg_right money (pow_nonneg gp.le _)
  have seam:=(winding hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead actors pieces physical
    P x A z hz inside F tag).2 {s} (fun _ => (1:ℂ)) (by intro j hj;have eq := Finset.mem_singleton.mp hj; subst j; exact ⟨live,wage⟩) (by simp)
  have seamPrice : ‖(Order.value (g:ℂ) (Order.ratio W)).part s-
      WilsonCoveredOrdinaryPolynomial.evaluated order K (g:ℂ) s‖ ≤ (ε/2)*g^q := by
    simpa only [Finset.sum_singleton,one_mul,g,K,writer,student,angle,W,issued] using seam
  have tr:=dist_triangle (Y.part s) ((Order.value (g:ℂ) (Order.ratio W)).part s)
    (WilsonCoveredOrdinaryPolynomial.evaluated order K (g:ℂ) s)
  simp only [dist_eq_norm] at tr
  refine ⟨fine,tr.trans ?_⟩
  calc
    _ ≤ (ε/2)*g^q + (ε/2)*g^q := add_le_add fine seamPrice
    _ = _ := by ring

end Grading
end YM.Integration.WilsonReceivedChargedOrdinaryReturn
