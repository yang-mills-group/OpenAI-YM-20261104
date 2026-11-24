import YM.Integration.WilsonFiniteOrdinaryTail
import YM.Integration.WilsonReceivedLogWindow

/-! The finite ordinary correlation on the elected Wilson programme. Each
partition uses the realized receipts of its own disjoint connected faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteOrdinaryWindow

open Multi WilsonIndependentOrdinaryPairGrade WilsonFiniteOrdinaryPartitions
open Finset Marker Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open scoped Classical BigOperators

section Finite
variable {V : Type} [Fintype V] [DecidableEq V] {J : Census V} {r : ℕ}

/-- The untruncated ordinary read is evaluated at the same source and the same
marked logarithm as the authenticated finite moment. -/
def difference (W : Grade J r) (y : ℂ) (s : J.Mode) :=
  (∑ q ∈ shards J s, ∏ t ∈ q.val, (Order.value y (Order.logMarked W)).part t.val)
    -(Order.value y (Order.ratio W)).part s

theorem funded (W : Grade J r) (unit : Order.UnitLeading W) (sym : Order.Symmetric W)
    (w : V → ℝ) (hw : ∀ v, 0 < w v) (g : ℝ) (gp : 0 < g) (small : g≤1)
    (paid : ∀ s : J.Mode,
      g*(Poly.toll w s * mass (slot s (Order.render (Order.logMarked W)))) ≤ 1)
    (s : J.Mode) (y : ℂ) (hy : ‖y‖≤1) :
    g^s.val.card*(Poly.toll w s*‖difference W y s‖) ≤
      ‖y‖^(r+1)*((shards J s).card:ℝ) := by
  let cost (t : J.Mode) := Poly.toll w t * mass (slot t (Order.render (Order.logMarked W)))
  have nn (t : J.Mode) : 0 ≤ cost t := mul_nonneg (Poly.worth hw _).le (IterationFour.Series.mass_nn _)
  have bounded (q : (parts J).Mode) (hit : q ∈ shards J s) :
      g^s.val.card*(∏t∈q.val,cost t.val) ≤ 1 := by
    have quoted : ∏t∈q.val,(g*cost t.val) ≤ 1 := by
      calc _ ≤ ∏_t∈q.val,(1:ℝ) := prod_le_prod (fun t _ => mul_nonneg gp.le (nn t.val))
                                  (fun t _ => paid t.val)
           _ = 1 := by simp
    rw [prod_mul_distrib,prod_const] at quoted
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (WilsonFiniteOrdinaryTail.blocks s q hit)
    rw [hd,pow_add]
    calc _ ≤ g^q.val.card * (∏t∈q.val,cost t.val) := mul_le_mul_of_nonneg_right
             (mul_le_of_le_one_right (pow_nonneg gp.le _) (pow_le_one₀ gp.le small)) (prod_nonneg (fun t _ => nn t.val))
         _ ≤ 1 := quoted
  have total : g^s.val.card*(∑q∈shards J s, ∏t∈q.val,cost t.val) ≤ ((shards J s).card:ℝ) := by
    rw [mul_sum]
    exact (sum_le_sum bounded).trans_eq (by simp)
  have read : (Poly.pass (Order.value y (Order.logMarked W))).part s =
      ∑ q ∈ shards J s, ∏ t ∈ q.val, (Order.value y (Order.logMarked W)).part t.val := by
    rw [←evaluated W unit]
    simp only [ordinary,Polynomial.eval_finsetSum,Polynomial.eval_prod,read_slot,←value_render]
  unfold difference
  rw [←read]
  calc
    _ ≤ g^s.val.card*(‖y‖^(r+1)*(∑q∈shards J s, ∏t∈q.val,cost t.val)) :=
      mul_le_mul_of_nonneg_left (WilsonFiniteOrdinaryTail.priced W unit sym w hw y hy s) (pow_nonneg gp.le _)
    _ ≤ _ := by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left total (by positivity)

omit [Fintype V] in
/-- Evaluating inside the measured coupling loses at most one power per
occupied source, independently of the torus and the number of RG dates. -/
theorem target {g a : ℝ} (gp : 0 < g) (small : g≤1) (s : J.Mode) (y : ℂ) (hy : ‖y‖≤g)
    (u : ℕ) (order : s.val.card+u ≤ r+1)
    (budget : g^s.val.card*a ≤ ‖y‖^(r+1)*((shards J s).card:ℝ)) :
    a ≤ g^u*((shards J s).card:ℝ) := by
  apply le_of_mul_le_mul_left _ (pow_pos gp s.val.card)
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le order
  calc
    _ ≤ _ := budget
    _ ≤ g^(r+1)*((shards J s).card:ℝ) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg y) hy _) (Nat.cast_nonneg _)
    _ ≤ g^(s.val.card+u)*((shards J s).card:ℝ) := by
      rw [hd,pow_add]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (pow_nonneg gp.le _)
        (pow_le_one₀ gp.le small)) (Nat.cast_nonneg _)
    _ = _ := by rw [pow_add,mul_assoc]
end Finite

open Filter Lattice Wilson RG Tree QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary ConnectedActivityE6
open scoped Topology

/-- The complete finite ordinary-mode tuition on the same before-cutoff
stage as the connected Jordan coefficients. -/
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
        ∀ s : (Stock.census V).Mode, let κ := Poly.toll P.w s
          (∀ y : ℂ, ‖y‖≤1 → g^s.val.card*(κ*‖difference W y s‖) ≤
            ‖y‖^(order+1)*((shards (Stock.census V) s).card:ℝ)) ∧
          ∀ u : ℕ, s.val.card+u ≤ order+1 →
            κ*‖difference W (g:ℂ) s‖ ≤ g^u*((shards (Stock.census V) s).card:ℝ) := by
  filter_upwards [WilsonReceivedLogWindow.original R simple D φ width grades order shelf k slots depth H cap hc,
    WilsonReceivedTaylorWindow.potential R simple depth H] with i income window
  intro m N per hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead X _ _ actors pieces physical P x A
    g B b angle z hz inside F tag issued W s κ
  have rates := income hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead actors pieces physical P x A
    z hz inside F tag
  have cheap : g≤1 := (window N per cut z hz).1
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have applyRate := funded W (Bulk.fk_unit ..) (Bulk.fk_sym ..) P.w P.issued.earning.positive g gp cheap
    (fun t => (rates t).1) s
  refine ⟨applyRate,fun u hu => ?_⟩
  have hnorm : ‖(g:ℂ)‖=g := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos gp]
  exact target gp cheap s (g:ℂ) hnorm.le u hu (applyRate _ (hnorm.le.trans cheap))

end YM.Integration.WilsonFiniteOrdinaryWindow
