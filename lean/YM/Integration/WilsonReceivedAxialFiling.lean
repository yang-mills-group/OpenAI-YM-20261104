import YM.Integration.WilsonReceivedAxialReporter
import YM.Integration.WilsonCapturedPrimaryPotential
import YM.Integration.WilsonOriginalReceivedPaidFolded

/-! Evaluate the issued unmasked physical source at the actual axial
extension. Its ordinary finite-order Taylor expense is bought on that
one source and one measured coupling, before the regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedAxialFiling
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

def opening {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ j k : ℕ, k ≤ j → ∀ b : ℝ, R.alloy.delay.betaEntry j ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) j)⁻¹ ^ 2) ≤ b)
    (order shelf seats : ℕ) {ε : ℝ} (ep : 0 < ε) : ℕ :=
  (eventually_atTop.mp (WilsonReceivedTaylorWindow.funded R simple D φ width order shelf 0 seats
    1 1 zero_le_one ep)).choose

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

include course cut in
theorem nominal (x : Wallet actors) (U : Config G (R.family.side i per)) :
    bare lamps x U = Integral.markedLog gf U (Air.craft student (fun b => (student b).paint x)
      grades (π i) tape) := by
  have hp : 0 < (R.family.path.rep N per (i+1)).beta := Overlay.beta_positive R.makes.wilson cut
  have gp : 0 < gf := inv_pos.mpr (Real.sqrt_pos.mpr hp)
  let inks := fun b => (student b).paint x
  have issued := Air.license student inks grades P.w P.issued.earning (Poetry.Agenda.stem ..)
    (fun b => P.issued.earning.honor b x)
  have reading := Air.liftPassport student inks grades issued (π i) tape gf gp.ne' U
  refine Eq.trans ?_ reading.tsum_eq
  unfold WilsonRootedKioskOccupiedSlip.bare
  apply tsum_congr
  intro b
  have shift := (course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).beta
  simp only [rendered,Air.grainR,Row.nominal,inks,shift]
  rfl

include course cut in
theorem tested (simple : G.Simple)
    (width : ∀ j k : ℕ, k ≤ j → ∀ b : ℝ, R.alloy.delay.betaEntry j ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) j)⁻¹ ^ 2) ≤ b)
    {ε : ℝ} (ep : 0 < ε) (late : opening R simple D φ width order shelf (Fintype.card V) ep ≤ i)
    (fit : k ≤ stage) (ξ : Directions G (R.family.side i per))
    (uniform : ∀ e, ‖ξ e‖ ≤ (Ψ i).p.threshold) {r : ℝ} (r0 : 0 ≤ r) (r1 : r ≤ 1) :
    let A := WilsonCapturedPrimaryPotential.potential gf (r • ξ)
    let angle := Stationary.arm G (R.family.side i per) 1 A
    Integral.sample gf angle = increment 1 (r • ξ) ∧ ∀ (x : Wallet actors) (s : (Stock.census V).Mode),
      let writer := Air.craft student (fun b => (student b).paint x) grades (π i) tape
      let folded := WilsonCoherentMayerWindingGrades.panel order (gf:ℂ) (fun j => Air.discharge writer j angle)
      Poly.toll P.w s*‖(bare lamps x (increment 1 (r • ξ))).part s-folded.part s‖ ≤ ε*gf^order := by
  intro A angle
  have gp : 0 < gf := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have sampled := WilsonCapturedPrimaryPotential.sampled gp (r • ξ)
  refine ⟨sampled,?_⟩
  intro x s writer folded
  let B := R.family.path.levels.budget i
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
  have charged := WilsonReceivedSourceRoster.original student P.w grades P.issued.earning
    (Poetry.Agenda.stem ..) x A (mul_nonneg zero_le_one (abs_nonneg z)) axis gp (π i) tape s
  have tariff := (eventually_atTop.mp (WilsonReceivedTaylorWindow.funded R simple D φ width order shelf
    0 (Fintype.card V) 1 1 zero_le_one ep)).choose_spec i late N per cut k fit z bound
  have price : 0 ≤ P.cost := Push.AbsoluteSums.budget_nonneg (P.salary.suggests 0)
  have rebate := P.issued.Waffle
  have cp : cap ≤ 1 := calc
    _ ≤ Ω*P.cost := mul_le_mul_of_nonneg_right rebate.earns price
    _ ≤ Ω*Ω⁻¹ := mul_le_mul_of_nonneg_left P.affordable (zero_le_one.trans rebate.cool)
    _ = _ := mul_inv_cancel₀ (zero_lt_one.trans_le rebate.cool).ne'
  have cost : 0 ≤ WilsonReceivedSourceRoster.tariff G σ (1*|z|) gf order shelf := by
    unfold WilsonReceivedSourceRoster.tariff;positivity
  have node : bare lamps x (increment 1 (r • ξ)) =
      Integral.markedLog gf (Integral.sample gf angle) writer :=
    (nominal R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades order shelf seats physical P x _).trans
      (congrArg (fun U => Integral.markedLog gf U writer) sampled.symm)
  rw [node]
  exact charged.trans ((mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left cp (Nat.cast_nonneg _)).trans (by
      rw [mul_one]
      exact_mod_cast Finset.card_image_le.trans (Finset.card_le_univ _))) cost).trans tariff)

end YM.Integration.WilsonReceivedAxialFiling
