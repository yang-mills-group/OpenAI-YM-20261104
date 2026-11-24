import YM.Integration.WilsonReceivedFiniteSingleton
import YM.Integration.WilsonReceivedSourceCoefficientWindow
import YM.Integration.WilsonOriginalAxialWinding

/-! The finite ordinary singleton on the physical reporting window, including the winding seam. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedSingletonWindow
open WilsonIndependentOrdinaryPairGrade
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

/-- On the original reporting course each normalized finite singleton costs one inverse power
of the measured coupling in its original source units, at every admitted physical panel node. -/
theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    {V : Type} [Fintype V] [DecidableEq V] (grades : V → ℕ)
    (order shelf k slots depth : ℕ) (H cap : ℝ) (hc : 0 ≤ cap) :
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
        ∀ a : V, let s := (Stock.census V).fire a
                 let κ := Poly.toll P.w s
                 g*(κ*mass (slot s (Order.render (Order.ratio W)))) ≤ 1 ∧
                   ∀ y : ℂ, ‖y‖≤1 → g*(κ*‖(Order.value y (Order.logMarked W)).part s‖) ≤ 1 := by
  let δ := ((order:ℝ)+1)⁻¹/2
  have dp : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [WilsonReceivedSourceCoefficientWindow.original R simple D φ width grades order shelf k slots depth
      1 H cap hc dp, WilsonReceivedTaylorWindow.potential R simple depth H,
      WilsonOriginalAxialWinding.eventually_open R simple 1 (2*cap) δ 0 0 0 1] with i rates window paid
  intro m N per hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead X _ _ actors pieces physical P x A
    g B b angle z hz inside F tag issued W a s κ
  let student := Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors P.model order P.voter
  let writer := Air.craft student (fun j => (student j).paint x) grades (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
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
    P.cost cost0 small A 1 (2*cap) δ 1 0 0 0 1 0 le_rfl (by positivity) dp
    (paid i le_rfl) zero_le_one (by simp) (by omega) axis
  have half : 2*seam ≤ δ := by simpa only [pow_zero,mul_one] using wind
  have seamBill : g*seam ≤ δ := calc
    _ ≤ g*δ := mul_le_mul_of_nonneg_left (by linarith only [half,dp] : seam ≤ δ) gp.le
    _ ≤ δ := mul_le_of_le_one_left dp.le cool
  have point (j : ℕ) (hj : j≤order) :
      g*(κ*‖(Air.discharge writer j angle).part s‖ + seam) ≤ δ+δ := by
    rw [mul_add]
    apply add_le_add _ seamBill
    simpa only [pow_one] using rates hk fit Q π Γ Ψ books hi cut ahead actors pieces physical P x A z hz inside j hj s
  have loaded : g * (∑ j∈range (order+1), (κ*‖(Air.discharge writer j angle).part s‖ + seam)) ≤ 1 := by
    rw [mul_sum]
    calc
      _ ≤ ∑ _j∈range (order+1), (δ+δ) := sum_le_sum (fun j hj => point j (Nat.le_of_lt_succ (mem_range.mp hj)))
      _ = 1 := by simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,δ]; field_simp; norm_num
  have finite := WilsonReceivedFiniteSingleton.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf slots physical P x A F tag a
  exact ⟨(mul_le_mul_of_nonneg_left finite.1 gp.le).trans loaded,
    fun y hy => (mul_le_mul_of_nonneg_left (finite.2 y hy) gp.le).trans loaded⟩

end YM.Integration.WilsonReceivedSingletonWindow
