import YM.Integration.WilsonReceivedOrdinaryFaces
import YM.Integration.WilsonReceivedOrdinaryHearing
import YM.Integration.WilsonFiniteOrdinaryWindow

/-! Ordinary physical moments at every occupied face of one original
received Wilson appointment, compared with its complete finite Wick table. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedOrdinaryPanel
open Filter Finset Multi Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Order
open Extra.Trajectories ConnectedActivityE6 WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators Topology

variable {V : Type} [DecidableEq V] [Fintype V] {J : Census V} {r : ℕ}

theorem measured_on (Y : Poly J) (unitY : Y.part J.quiet = 1)
    (W : Grade J r) (unit : UnitLeading W) (sym : Symmetric W)
    (w : V → ℝ) (hw : ∀ v, 0 < w v) (g E : ℝ) (gp : 0<g) (small : g≤1) (ep : 0≤E) (s : J.Mode)
    (massPaid : ∀ d : Multi.Hot J, d.val.val ⊆ s.val →
      g*(Poly.toll w d.val * mass (slot d.val (Order.render (Order.logMarked W)))) ≤ 1)
    (changes : ∀ d : Multi.Hot J, d.val.val ⊆ s.val → Poly.toll w d.val *
      ‖(Order.logTo (Fintype.card V) Y - Order.value (g:ℂ) (Order.logMarked W)).part d.val‖ ≤ E)
    (u : ℕ) (grades : s.val.card+u ≤ r+1) :
    Poly.toll w s * ‖Y.part s - (Order.value (g:ℂ) (Order.ratio W)).part s‖ ≤
      (∑ h∈shards J s,(h.val.card:ℝ)*E*(g⁻¹+E)^h.val.card) + g^u*(shards J s).card := by
  let T := Order.value (g:ℂ) (Order.logMarked W)
  have normg : ‖(g:ℂ)‖ = g := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos gp]
  have t₀ : T.part J.quiet = 0 := by
    have h : Poly.bead J (T.part J.quiet)=0 := by
      dsimp only [T]
      rw [←value_denom,denominator,log_marked unit]
      exact (valueL J r (g:ℂ)).map_zero
    simpa using congrArg (Poly.part · J.quiet) (show Poly.send J.quiet _=0 from h)
  have scale : 1 ≤ g⁻¹+E := (one_le_inv_iff₀.mpr ⟨gp,small⟩).trans (le_add_of_nonneg_right ep)
  let cost (d : Multi.Hot J) := Poly.toll w d.val * mass (slot d.val (Order.render (Order.logMarked W)))
  have purchase (d : Multi.Hot J) (hd : d.val.val ⊆ s.val) : cost d ≤ g⁻¹ := by
    rw [←one_div]
    exact (le_div_iff₀ gp).2 ((mul_comm _ g).le.trans (massPaid d hd))
  have filed (d : Multi.Hot J) (hd : d.val.val ⊆ s.val) : Poly.toll w d.val * ‖T.part d.val‖ ≤ g⁻¹ :=
    (mul_le_mul_of_nonneg_left (WilsonReceivedLogWindow.measuredMass _ _ _ (normg.le.trans small))
      (Poly.worth hw _).le).trans (purchase d hd)
  have before := log_to Y unitY (Fintype.card V) (fun t => card_le_univ t.val)
  have step := WilsonReceivedOrdinaryFaces.ordinary_on (connected Y) T w hw (connected_quiet unitY)
    t₀ E g⁻¹ ep scale s (fun d hd=>by rw [before]; exact changes d hd) filed
  rw [pass_connected unitY] at step
  have bound (h : (Multi.parts J).Mode) (hh : h ∈ shards J s) :
      (∏ d∈h.val,cost d) ≤ g⁻¹^s.val.card := calc
    _ ≤ ∏ _d∈h.val,g⁻¹ := Finset.prod_le_prod
      (fun d _ => mul_nonneg (Poly.worth hw _).le (IterationFour.Series.mass_nn _))
      (fun d hd => purchase d (WilsonReceivedOrdinaryFaces.contained s h hh d hd))
    _ = g⁻¹^h.val.card := prod_const ..
    _ ≤ _ := pow_le_pow_right₀ (one_le_inv_iff₀.mpr ⟨gp,small⟩) (WilsonFiniteOrdinaryTail.blocks s h hh)
  have price : g^(r+1)*g⁻¹^s.val.card ≤ g^u := calc
    _ ≤ g^(s.val.card+u)*g⁻¹^s.val.card := mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one gp.le small grades) (pow_nonneg (inv_nonneg.mpr gp.le) _)
    _ = _ := by rw [pow_add,inv_pow]; field_simp
  have tail := WilsonFiniteOrdinaryTail.priced W unit sym w hw (g:ℂ) (normg.le.trans small) s
  rw [normg] at tail
  have affordable : Poly.toll w s * ‖(Poly.pass T).part s - (Order.value (g:ℂ) (Order.ratio W)).part s‖ ≤
      g^u*(shards J s).card := calc
    _ ≤ g^(r+1)*∑ h∈shards J s,∏ d∈h.val,cost d := tail
    _ ≤ g^(r+1)*∑ _h∈shards J s,g⁻¹^s.val.card :=
      mul_le_mul_of_nonneg_left (sum_le_sum bound) (pow_nonneg gp.le _)
    _ = (g^(r+1)*g⁻¹^s.val.card)*(shards J s).card := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right price (Nat.cast_nonneg _)
  have triangle := dist_triangle (Y.part s) ((Poly.pass T).part s) ((Order.value (g:ℂ) (Order.ratio W)).part s)
  simp only [dist_eq_norm] at triangle
  exact (mul_le_mul_of_nonneg_left triangle (Poly.worth hw s).le).trans
    ((mul_add ..).le.trans (add_le_add step affordable))

theorem measured (Y : Poly J) (unitY : Y.part J.quiet = 1)
    (W : Grade J r) (unit : UnitLeading W) (sym : Symmetric W)
    (w : V → ℝ) (hw : ∀ v, 0 < w v) (g E : ℝ) (gp : 0<g) (small : g≤1) (ep : 0≤E)
    (massPaid : ∀ s : J.Mode, g*(Poly.toll w s * mass (slot s (Order.render (Order.logMarked W)))) ≤ 1)
    (changes : ∀ d : Multi.Hot J, Poly.toll w d.val *
      ‖(Order.logTo (Fintype.card V) Y - Order.value (g:ℂ) (Order.logMarked W)).part d.val‖ ≤ E)
    (s : J.Mode) (u : ℕ) (grades : s.val.card+u ≤ r+1) :
    Poly.toll w s * ‖Y.part s - (Order.value (g:ℂ) (Order.ratio W)).part s‖ ≤
      (∑ h∈shards J s,(h.val.card:ℝ)*E*(g⁻¹+E)^h.val.card) + g^u*(shards J s).card :=
  measured_on Y unitY W unit sym w hw g E gp small ep s (fun d _=>massPaid d.val)
    (fun d _=>changes d) u grades

/-- One onset for every field, forest, tag, position and subset. Both the
true ordinary face and the finite Wick face use this post's complete input. -/
theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    (grades : V → ℕ) (q depth order shelf k slots : ℕ)
    (deep : 2*(q+1)+8 ≤ order) (aged : q+4 ≤ 3*k+2) (H cap : ℝ) (hc : 0≤cap) {ε : ℝ} (ep : 0<ε) :
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
      let angle := Stationary.arm G (R.family.side i per) 1 A
      ∀ z : ℝ, |z| ≤ |H| * (Real.log (R.family.path.levels.clock.hatBeta i))^depth*((B.B:ℝ)^2*B.threshold)/g →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap*|z|) →
        let U := Integral.sample g angle
        flags (Ψ i).p.threshold U = ∅ →
        ∀ (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices),
        let issued := Air.craft P.model (fun j => (P.model j).paint x) grades (π (i+1))
          (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let W := Bulk.Fk ((RunFormalChain.fromRun R).step N i per cut) F tag issued angle order
        let Y := (((Ψ i).eval U:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i (physical x) U
        let E := (8*(budgetR R i)^slots)*P.rent+ε*g^q
        ∀ (s : (Stock.census V).Mode) (u : ℕ), s.val.card+u ≤ order+1 →
          Poly.toll P.w s * ‖Y.part s - (Order.value (g:ℂ) (Order.ratio W)).part s‖ ≤
            (∑ h∈shards (Stock.census V) s,(h.val.card:ℝ)*E*(g⁻¹+E)^h.val.card) +
              g^u*(shards (Stock.census V) s).card := by
  let onset (d : Multi.Hot (Stock.census V)) := (eventually_atTop.mp
    (WilsonReceivedPaidCourse.original R simple D φ width grades d.val d.property.choose d.property.choose_spec
      q depth order shelf k slots deep aged H cap hc ep)).choose
  have ready : ∀ᶠ i : ℕ in atTop, ∀ d : Multi.Hot (Stock.census V), onset d ≤ i :=
    eventually_all.mpr (fun d=>eventually_ge_atTop (onset d))
  filter_upwards [ready,WilsonReceivedLogWindow.original R simple D φ width grades order shelf k slots depth H cap hc,
    WilsonReceivedTaylorWindow.potential R simple depth H] with i late massBound window
  intro m N per hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead X _ _ actors pieces physical P x A
    g B angle z hz inside U healthy F tag issued W Y E s u hu
  letI := P.modelCount
  let vacuum := (((Ψ i).eval U:ℂ)⁻¹)
  have normed : Y.part (Stock.census V).quiet = 1 := by
    have output := congrFun (WilsonOriginalReceivedChain.report R hk D Q π Γ Ψ books ahead actors pieces grades
      order shelf slots i hi physical P x) U
    exact (congrArg (fun d => (vacuum • d).part (Stock.census V).quiet) output).trans
      (WilsonReceivedOrdinaryHearing.clear _ x U healthy)
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have cheap : g≤1 := (window N per cut z hz).1
  have budget : 0≤budgetR R i := (by norm_num : (0:ℝ)≤4).trans
    (P.issued.Waffle.strong.trans P.issued.Beamwork)
  have E₀ : 0 ≤ E := add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg budget _)) P.active.le)
    (mul_nonneg ep.le (pow_nonneg gp.le _))
  apply measured Y normed W (Bulk.fk_unit ..) (Bulk.fk_sym ..) P.w P.salary.positive g E gp cheap E₀
    (fun v=>(massBound hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead actors pieces physical P x A
      z hz inside F tag v).1) _ s u hu
  intro d
  have price := WilsonReceivedPostLog.original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf slots i hi
    physical simple width course law enrolled fund cut fit P d.val d.property.choose d.property.choose_spec q depth
    deep aged H cap hc ep (late d) x F tag A z hz inside healthy
  exact (mul_comm _ _).le.trans ((le_div_iff₀ (Poly.worth P.salary.positive d.val)).mp price)

end YM.Integration.WilsonReceivedOrdinaryPanel
