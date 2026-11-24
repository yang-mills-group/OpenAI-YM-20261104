import YM.Integration.WilsonReceivedAxialFiling
import YM.Integration.WilsonReceivedOrdinaryPanel

/-! The signed finite versus folded Wick bill and coefficient masses on the
actual moving axial chart, uniformly in both original regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedAxialFinite
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Ac OPE.Therm WilsonLimitConstruction RG16 MSbar.Heath Labels Source Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare
open scoped Classical BigOperators Topology

open WilsonIndependentOrdinaryPairGrade Comparison.RG02.Cumulants

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "stage" => R.alloy.B.a.clock.J i
local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) stage
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "cap" => (fig).produce (R.family.path.levels.clock.op i per).ratio.count * P.cost
local notation "placed" => P.passport.coarser (R.family.path.levels.clock.op i per).ratio

def opening (simple : G.Simple) (q : ℕ) {ε : ℝ} (_ep : 0 < ε) : ℕ :=
  max (WilsonCoherentMayerRosterWindingRun.firstDate R simple)
    (max (eventually_atTop.mp (WilsonReceivedTaylorWindow.potential R simple 0 1)).choose
      (eventually_atTop.mp (WilsonOriginalAxialWinding.eventually_open R simple 1 (2*1) ε 0 0 q 1)).choose)

def massOpening (simple : G.Simple)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b) : ℕ :=
  (eventually_atTop.mp (WilsonReceivedLogWindow.original R simple D φ width grades order shelf k seats 0 1 1 zero_le_one)).choose

include course hi cut in
theorem room (ξ : Directions G (R.family.side i per))
    (uniform : ∀ e, ‖ξ e‖ ≤ (Ψ i).p.threshold) {r : ℝ} (r0 : 0 ≤ r) (r1 : r ≤ 1) :
    let B := R.family.path.levels.budget i
    let A := WilsonCapturedPrimaryPotential.potential gf (r • ξ)
    let angle := Stationary.arm G (R.family.side i per) 1 A
    ∃ z : ℝ, |z| ≤ |(1:ℝ)| * (Real.log (R.family.path.levels.clock.hatBeta i))^0*
      ((B.B:ℝ)^2*B.threshold)/gf ∧ ∀ e, ‖Exterior.collect G angle e‖ ≤ (1:ℝ)*|z| := by
  intro B A angle
  have gp : 0 < gf := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have point : (Ψ i).p = B := (course.1.walk i hi cut.le).truep.point
  let z := r*B.threshold/gf
  have zp : 0 ≤ z := div_nonneg (mul_nonneg r0 B.threshold_pos.le) gp.le
  have rb : r ≤ (B.B:ℝ)^2 := r1.trans (one_le_pow₀ (by exact_mod_cast B.B_pos) (n:=2))
  have bound : |z| ≤ |(1:ℝ)| * (Real.log (R.family.path.levels.clock.hatBeta i))^0*
      ((B.B:ℝ)^2*B.threshold)/gf := by
    simp only [abs_of_nonneg zp,abs_one,pow_zero,one_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right rb B.threshold_pos.le) gp.le
  have axis (e) : ‖Exterior.collect G angle e‖ ≤ (1:ℝ)*|z| := by
    rw [one_mul,abs_of_nonneg zp]
    change ‖Exterior.collect G (Stationary.arm G _ 1 (WilsonCapturedPrimaryPotential.potential gf (r • ξ))) e‖ ≤ _
    rw [WilsonCapturedPrimaryPotential.scaled]
    change ‖gf⁻¹ • (r • ξ e)‖ ≤ _
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr gp),abs_of_nonneg r0]
    rw [point] at uniform
    simpa only [z,div_eq_mul_inv,mul_comm (a:=_ * _)] using
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (uniform e) r0) (inv_pos.mpr gp).le
  exact ⟨z,bound,axis⟩

include course cut in
theorem priced (simple : G.Simple)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    (law : VowsR.LawScroll G φ) (enrolled : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (q : ℕ) {ε : ℝ} (ep : 0 < ε)
    (late : max (opening R simple q ep)
      (massOpening R D grades order shelf seats (k:=k) simple width) ≤ i)
    (fit : k ≤ stage) (ξ : Directions G (R.family.side i per))
    (uniform : ∀ e, ‖ξ e‖ ≤ (Ψ i).p.threshold) {r : ℝ} (r0 : 0 ≤ r) (r1 : r ≤ 1) :
    let A := WilsonCapturedPrimaryPotential.potential gf (r • ξ)
    let angle := Stationary.arm G (R.family.side i per) 1 A
    gf ≤ 1 ∧ ∀ (x : Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
      (tag : (R.family.path.levels.clock.op i per).Choices),
      let issued := Air.craft P.model (fun b => (P.model b).paint x) grades (π (i+1)) tape
      let W := Bulk.Fk ((RunFormalChain.fromRun R).step N i per cut) F tag issued angle order
      let writer := Air.craft student (fun b => (student b).paint x) grades (π i) tape
      let folded := WilsonCoherentMayerWindingGrades.panel order (gf:ℂ) (fun j => Air.discharge writer j angle)
      let finite := Order.value (gf:ℂ) (Order.logMarked W)
      Poly.price P.w (folded-finite) ≤ ε*gf^q ∧
        ∀ s : (Stock.census V).Mode,
          gf*(Poly.toll P.w s*mass (slot s (Order.render (Order.logMarked W)))) ≤ 1 := by
  intro A angle
  obtain ⟨hz,hM⟩ := max_le_iff.mp late
  obtain ⟨hF,hz⟩ := max_le_iff.mp hz
  obtain ⟨hW,hP⟩ := max_le_iff.mp hz
  obtain ⟨z,bound,axis⟩ := room R π Γ Ψ course hi cut ξ uniform r0 r1
  obtain ⟨cool,top⟩ := (eventually_atTop.mp (WilsonReceivedTaylorWindow.potential R simple 0 1)).choose_spec i hW N per cut z bound
  refine ⟨cool,?_⟩
  intro x F tag issued W writer folded finite
  have small := P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool)
  have nonnegative := Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  let upper := R.alloy.B.a.clock.hatBeta (i+1)
  have axes (e) : ‖Exterior.collect G angle e‖ ≤ (2*1)*upper^1 := calc
    _ ≤ (1:ℝ)*|z| := axis e
    _ ≤ 1*(2*upper) := mul_le_mul_of_nonneg_left top zero_le_one
    _ = _ := by ring
  have seam := WilsonOriginalAxialWinding.measured R hk D Q π Γ law books enrolled fund hi cut P.op P.lesson
    P.cost nonnegative small A 1 (2*1) ε 1 0 0 q 1 0 le_rfl (by positivity) ep
    ((eventually_atTop.mp (WilsonOriginalAxialWinding.eventually_open R simple 1 (2*1) ε 0 0 q 1)).choose_spec i hP i le_rfl)
    zero_le_one (by simp) (by omega) axes
  simp only [pow_zero,mul_one] at seam
  obtain ⟨_,certified⟩ := WilsonOriginalMarkedEvaluation.assessed R hk D Q π Γ Ψ course
    books hi cut P.op P.lesson ahead actors P.model P.w grades order shelf P.voter P.cost P.salary
    x F tag A pieces P.input P.rent P.output P.issued small simple (hF.trans (Nat.le_succ _))
  have legal : Legal tape (π (i+1)) := by
    rw [P.lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ P.lesson.entry
  have staff := Air.license P.model (fun b => (P.model b).paint x) grades P.w P.salary
    (Poetry.Agenda.stem ..) (fun b => P.salary.honor b x)
  have well := (Air.standard P.model _ grades staff (π (i+1)) tape legal).1
  constructor
  · change Poly.price P.w (folded-Order.value (gf:ℂ) (Order.logMarked (Bulk.Fk _ F tag issued angle order))) ≤ _
    rw [PhysicalWilsonPeriodizedMaterial.original R N i per cut angle issued order F tag well]
    exact certified.2.2.2.2.trans seam
  · intro s
    exact ((eventually_atTop.mp (WilsonReceivedLogWindow.original R simple D φ width grades order shelf k seats
      0 1 1 zero_le_one)).choose_spec i hM hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead actors pieces
      physical P x A z bound axis F tag s).1

end YM.Integration.WilsonReceivedAxialFinite
