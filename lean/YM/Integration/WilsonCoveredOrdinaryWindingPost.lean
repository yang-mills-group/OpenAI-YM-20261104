import YM.Integration.WilsonCoveredOrdinaryWinding

/-! Signed finite-minus-cover winding for every original paid logarithmic coefficient and its
truncated ordinary moment on the true held angle, retaining every proper source radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoveredOrdinaryWindingPost
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
    (order shelf k slots depth power : ℕ) (H cap : ℝ) (hc : 0 ≤ cap) {ε : ℝ} (ep:0<ε) :
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
        (∀ l,l≤order → ∀s: (Stock.census V).Mode,Poly.toll P.w s*
          ‖(Order.observe _ order (Order.logMarked W) l).part s-(K l).part s‖≤
            (ε/((order:ℝ)+1))*g^power) ∧
        ∀ s:(Stock.census V).Mode, (∀d:Multi.Hot (Stock.census V), d.val.val ⊆ s.val →
          g*(Poly.toll P.w d.val*mass (slot d.val (Order.render (Order.logMarked W))))≤1) → Poly.toll P.w s*‖(Order.value (g:ℂ) (Order.ratio W)).part s-
            WilsonCoveredOrdinaryPolynomial.evaluated order K (g:ℂ) s‖≤
          ∑h∈shards (Stock.census V) s,(h.val.card:ℝ)*(ε*g^power)*(g⁻¹+ε*g^power)^h.val.card := by
  let δ := ε/((order:ℝ)+1)
  have dp : 0<δ := by dsimp [δ]; positivity
  filter_upwards [WilsonReceivedTaylorWindow.potential R simple depth H,
    WilsonOriginalAxialWinding.eventually_open R simple 1 (2*cap) δ 0 0 power 1] with i window paid
  intro m N per hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead X _ _ actors pieces physical P x A
    g B b angle z hz inside F tag issued W student writer K
  let seam := Oak.Tutoring.bill R hk D Q π Γ books hi P.op P.lesson A P.cost
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  obtain ⟨cool,top⟩ := window N per (Nat.succ_le_of_lt cut) z hz
  have small := P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool)
  have cost0 := Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  let upper := R.alloy.B.a.clock.hatBeta (i+1)
  have axis (e) : ‖Exterior.collect G angle e‖ ≤ 2*cap*upper^1 := calc
    _ ≤ cap*|z| := inside e
    _ ≤ cap*(2*upper) := mul_le_mul_of_nonneg_left top hc
    _ = _ := by ring
  have wind := WilsonOriginalAxialWinding.measured R hk D Q π Γ law books enrolled fund hi cut P.op P.lesson
    P.cost cost0 small A 1 (2*cap) δ 1 0 0 power 1 0 le_rfl (by positivity) dp
    (paid i le_rfl) zero_le_one (by simp) (by omega) axis
  have half : 2*seam ≤ δ*g^power := by simpa only [pow_zero,mul_one] using wind
  have bound : seam≤δ*g^power := by
    rcases le_total seam 0 with h|h
    · exact h.trans (mul_nonneg dp.le (pow_nonneg gp.le _))
    · linarith only [half,h]
  obtain ⟨calendar⟩ := Oak.agrees R hk D Q π Γ Ψ course hi cut P.lesson
  have each (l:ℕ)(hl:l≤order)(s:(Stock.census V).Mode) :
      Poly.toll P.w s*‖(Order.observe _ order (Order.logMarked W) l).part s-(K l).part s‖≤δ*g^power := by
    letI : Countable P.modelIndex := P.modelCount
    obtain ⟨e,eqn,price,_⟩:=Oak.Tutoring.fund R hk D Q π Γ Ψ books hi cut P.op P.lesson calendar ahead
      actors P.model P.w grades order shelf P.voter P.cost P.salary x F tag l A hl small _ P.issued.earning
    rw [show Order.observe _ order (Order.logMarked W) l=K l+e from eqn]
    change Poly.toll P.w s*‖(K l).part s+e.part s-(K l).part s‖≤_
    rw [add_sub_cancel_left]
    exact (Poly.member P.issued.earning.positive s e).trans (price.trans bound)
  refine ⟨each,?_⟩
  intro s paidMass
  have filed (d:Multi.Hot (Stock.census V)) (hd:d.val.val⊆s.val) :
      Poly.toll P.w d.val*mass (WilsonCoveredOrdinaryPolynomial.row order
        (fun l=>(Order.observe _ order (Order.logMarked W) l).part d.val))≤g⁻¹ := by
    rw [WilsonCoveredOrdinaryPolynomial.finite_row,←one_div]
    apply (le_div_iff₀ gp).2
    exact (mul_comm _ g).le.trans (paidMass d hd)
  have normg : ‖(g:ℂ)‖=g := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos gp]
  have cold : g≤1 := cool
  have tight:=WilsonCoveredOrdinaryWinding.priced order (Order.observe _ order (Order.logMarked W)) K
    (g:ℂ) (normg.le.trans cold) s P.w
    P.issued.earning.positive g⁻¹ (δ*g^power) (one_le_inv_iff₀.mpr ⟨gp,cold⟩)
    (mul_nonneg dp.le (pow_nonneg gp.le _)) filed (fun d _ l hl=>each l hl d.val)
  have unit : Order.UnitLeading W := Bulk.fk_unit ..
  have sym : Order.Symmetric W := Bulk.fk_sym ..
  rw [WilsonCoveredOrdinaryPolynomial.finite W unit sym] at tight
  have cash:((order:ℝ)+1)*(δ*g^power)=ε*g^power := by dsimp [δ]; field_simp
  simpa only [cash] using tight

end Grading
end YM.Integration.WilsonCoveredOrdinaryWindingPost
