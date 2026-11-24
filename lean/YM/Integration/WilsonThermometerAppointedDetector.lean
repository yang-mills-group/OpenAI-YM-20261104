import YM.Integration.WilsonThermometerFirstJoinAppointment
import YM.Integration.WilsonThermometerOfferedStep
import YM.Integration.WilsonThermometerFirstRent
import YM.Integration.WilsonOriginalThermometerReportedRefund
import YM.Integration.WilsonOriginalThermometerReportedToll

/-! Recast the selected old-hard appointment as the literal original detector
source, preserving its gallery and returning the genuine restored test budget. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerHeldSource
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology
open WilsonThermometerCourseHearing
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
    {m N per k i : ℕ} (live : i < N) (o : Positions (Fin 3) (R.family.side N per))
    (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
    (ahead : Mentor.Forecast D R.rolls Q φ books) (order shelf seats : ℕ) (floor : m ≤ i)
local notation "ages" => (fun u : Fin 3 => (grade u).val)
variable (observed : Wallet disks → Config G (R.family.side (i+1) per) → Poly (Stock.census (Fin 3)))
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead disks sectors ages
  order shelf seats i floor observed)
open Progress.DirectedRecipe QuadraticLocal.Tint OPE.Therm

theorem actual (same : observed=offered R A simple live o) :
    ∃ L : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead disks sectors ages order shelf
      seats i floor (offered R A simple live o),
      HEq L P ∧ L.w=P.w ∧ L.rent=P.rent ∧ L.op=P.op ∧ L.lesson=P.lesson ∧
        HEq L.input P.input ∧ HEq L.output P.output := by
  subst observed
  exact ⟨P,HEq.rfl,rfl,rfl,rfl,rfl,HEq.rfl,HEq.rfl⟩

end YM.Integration.WilsonThermometerHeldSource
end

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAppointedDetector
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity QuadraticLocal.Tint Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology

open WilsonThermometerCourseHearing WilsonPositionThermometerGradedReading LocalComparison ActualPolynomialContraction MergeProof.Accent
open WilsonOriginalStarSceneRent WilsonOriginalThermometerTollBudget
open WilsonOriginalThermometerMicroscopic


variable {G : Gauge} (R : Run G) {m j per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  (order shelf seats : ℕ) (floor : m ≤ j) (A : Group R.family 6)
  (simple : G.Simple) (cut : j+1<(j+2)) (o : Positions (Fin 3) (R.family.side (j+2) per))
local notation "actors" => disks
local notation "pieces" => sectors
local notation "grades" => (fun z : Fin 3 => (grade z).val)

variable (P : Post (N:=(j+2)) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
    (floor.trans (Nat.le_succ j)) (offered R A simple cut o))

local notation "earlier" => (fun x : Wallet actors => LocalComparison.actualPush R.family (j+2) per (j+1) ((offered R A simple cut o) x))
local notation "elected" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) P.op P.lesson ahead order shelf
local notation "hi" => floor.trans (Nat.le_succ j)
variable [Countable P.inputIndex]
  (course:Concourse R.alloy R.kit R.T π Γ m (j+2) per k Ψ)
  (scroll:VowsR.LawScroll G φ) (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
  (load:P.op.count≤Burn.horizon k+2) (wide:shelf≤R.alloy.B.a.clock.J (j+1)) (test:Wallet actors)
local notation "initial" op:max => op R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1)
  (floor.trans (Nat.le_succ j)) (offered R A simple cut o) P simple cut course scroll chamber hospital load wide test
local notation "issued" => initial WilsonOriginalReceivedFirstEnrollment.installed
local notation "coarsePost" => Post (N:=(j+2)) (V:=Fin 3) (X:=fun _ => ℂ) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor earlier
local notation "wallet₀" => max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R j 1)*
  wallet R WilsonOriginalThermometerPalette.levels (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+2))))
local notation "physical" => offered R A simple (Nat.lt_of_succ_lt cut) o
local notation "target" => WilsonOriginalReceivedChain.Post (N:=(j+2)) (V:=Fin 3) (X:=fun _ => ℂ)
  R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor (physical)

variable {h C E : ℝ} (q : ℕ)
  (receipt : WilsonThermometerFirstJoinAppointment.Record R hk D Q π Γ Ψ books ahead order shelf seats floor
    A simple cut o P course scroll chamber hospital load wide test (q+1) 1 h C E ((Coat.gStep (R.family.path.rep (j+2) per (j+2)).beta)^(q+1)))

def activation {G : Gauge} (R : Run G) (simple : G.Simple) (q seats : ℕ) {ε : ℝ} (ep : 0 < ε) : ℕ :=
  max (eventually_atTop.mp (WilsonOriginalThermometerReportedRefund.original R simple)).choose
    (eventually_atTop.mp (WilsonMovingMentorPageCoupling.repaid R simple seats q
      (div_pos ep (by positivity : 0 < 16*(2:ℝ)^(q+1))))).choose

private theorem smaller (h E b : ℝ) (one : 1 ≤ h) (b₀ : 0 ≤ b) (cap : E ≤ 2*b) :
    max (h⁻¹*E) b ≤ 2*b := by
  have h₀ : 0 ≤ h⁻¹ := inv_nonneg.mpr (zero_le_one.trans one)
  apply max_le
  · exact (mul_le_mul_of_nonneg_left cap h₀).trans (mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ one))
  · linarith only [b₀]

private theorem rented {ε : ℝ} (ep : 0 < ε) (late : activation R simple q seats ep ≤ j)
    (bare : P.rent=(Coat.gStep (R.family.path.rep (j+2) per (j+2)).beta)^(q+1)) :
    (8*(Oak.expenseReal R hk D Q π Γ books floor receipt.post.op receipt.post.lesson ahead order shelf)^seats)*receipt.post.rent ≤ ε*(Coat.gStep (R.family.path.rep (j+2) per (j+1)).beta)^q := by
    let gt := Coat.gStep (R.family.path.rep (j+2) per (j+2)).beta
    let gs₀ := Coat.gStep (R.family.path.rep (j+2) per (j+1)).beta
    let Ω := Oak.expenseReal R hk D Q π Γ books floor receipt.post.op receipt.post.lesson ahead order shelf
    let c := 16*(2:ℝ)^(q+1)
    have cp : 0 < c := by dsimp [c]; positivity
    let δ := ε/c
    have dp : 0 < δ := div_pos ep cp
    have Ω0 : 0 ≤ Ω := zero_le_one.trans receipt.post.issued.Waffle.cool
    have many := (eventually_atTop.mp (WilsonMovingMentorPageCoupling.repaid R simple seats q dp)).choose_spec
      j ((le_max_right ..).trans late) Ω Ω0 (receipt.post.issued.Beamwork.trans (min_le_right ..)) (j+2) per (by omega)
    change Ω^seats*gs₀^(q+1) ≤ δ*gs₀^q at many
    have right : gt ≤ 2*gs₀ := WilsonLocalCompactRichPortUnits.compared R simple
      (show j+1 ≤ j+2 by omega) (show j+2 ≤ j+2 by omega) per
    have gt0 : 0 ≤ gt := (ActualRunKernelPackets.regulator_pos R (j+2) per (j+2) cut).le
    have bound : E ≤ 2*gt^(q+1) := by simpa only [bare,one_mul,←two_mul] using receipt.oldBudget
    have rent : receipt.post.rent ≤ 2*gt^(q+1) := by
      rw [receipt.salary]
      exact smaller h E _ receipt.full (pow_nonneg gt0 _) bound
    change (8*Ω^seats)*receipt.post.rent ≤ ε*gs₀^q
    have scale : c*δ=ε := by simp [δ,div_eq_mul_inv,cp.ne',mul_left_comm]
    calc
      _ ≤ (8*Ω^seats)*(2*gt^(q+1)) := mul_le_mul_of_nonneg_left rent (by positivity)
      _ ≤ (8*Ω^seats)*(2*(2*gs₀)^(q+1)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ gt0 right _) (by norm_num)) (by positivity)
      _ = c*(Ω^seats*gs₀^(q+1)) := by dsimp only [c];rw [mul_pow];ring
      _ ≤ c*(δ*gs₀^q) := mul_le_mul_of_nonneg_left many cp.le
      _ = _ := by rw [←mul_assoc,scale]

private theorem refunded (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    {ε : ℝ} (ep : 0 < ε) (late : activation R simple q seats ep ≤ j)
    (extent : reach R ≤ R.alloy.B.a.clock.J (j+2)+1) (bare : P.rent=(Coat.gStep (R.family.path.rep (j+2) per (j+2)).beta)^(q+1))
    (wages : ∀ a : Fin 3, P.w a=(wallet₀*elected)⁻¹) :
    ∀ s : (Stock.census (Fin 3)).Mode, (Coat.gStep (R.family.path.rep (j+2) per (j+1)).beta)^157 ≤ Poly.toll receipt.post.w s := by
    have rich : 1 ≤ elected := P.issued.Waffle.cool
    have unit : 1 ≤ wallet₀*elected := one_le_mul_of_one_le_of_one_le (le_max_left _ _) rich
    have ready := (Nat.le_add_right (Burn.horizon k) 2).trans
      (hk.trans (R.alloy.B.a.fits.mono (floor.trans (show j ≤ j+2 by omega))))
    have price := WilsonOriginalThermometerReportedToll.original R simple D φ income j (Burn.horizon k)
      ready extent (zero_le_one.trans rich) P.issued.Beamwork
    have shrink := receipt.budget
    simp only [one_mul] at shrink
    have ceiling : P.rent+Coat.gStep (R.family.path.rep (j+2) per (j+2)).beta^(q+1) ≤ 2 := by
      rw [←bare]
      linarith only [P.small]
    have all := (eventually_atTop.mp (WilsonOriginalThermometerReportedRefund.original R simple)).choose_spec
      j ((le_max_left ..).trans late) per (wallet₀*elected) (elected) h _
      (zero_lt_one.trans_le unit) price rich P.issued.Beamwork receipt.full shrink ceiling P.w receipt.post.w
      wages receipt.weights
    exact all.2


theorem original (refs : ∀ a : Fin 3, R.family.ref (grade a) ≤ (j+2))
    (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay) {ε : ℝ}
    (ep : 0 < ε) (late : activation R simple q seats ep ≤ j)
    (extent : reach R ≤ R.alloy.B.a.clock.J (j+2)+1) (bare : P.rent=(Coat.gStep (R.family.path.rep (j+2) per (j+2)).beta)^(q+1))
    (wages : ∀ a : Fin 3, P.w a=(wallet₀*elected)⁻¹) :
    ∃ L : target, HEq L receipt.post ∧ L.w=receipt.post.w ∧ L.rent=receipt.post.rent ∧
      L.op=receipt.post.op ∧ L.lesson=receipt.post.lesson ∧ HEq L.input receipt.post.input ∧
      HEq L.output receipt.post.output ∧
      (8*(Oak.expenseReal R hk D Q π Γ books floor L.op L.lesson ahead order shelf)^seats)*L.rent ≤ ε*(Coat.gStep (R.family.path.rep (j+2) per (j+1)).beta)^q ∧
      ∀ s : (Stock.census (Fin 3)).Mode, (Coat.gStep (R.family.path.rep (j+2) per (j+1)).beta)^157 ≤ Poly.toll L.w s := by
  obtain ⟨L,same,w,paid,opEq,lessonEq,old,hard⟩ := WilsonThermometerHeldSource.actual R A simple
    (Nat.lt_of_succ_lt cut) o hk D Q π Γ Ψ books ahead order shelf seats floor earlier receipt.post
    (WilsonThermometerOfferedStep.original R A simple cut o refs)
  refine ⟨L,same,w,paid,opEq,lessonEq,old,hard,?_,?_⟩
  · simpa only [opEq,lessonEq,paid] using (rented R hk D Q π Γ Ψ books ahead order shelf seats floor A simple cut o P course scroll chamber hospital load wide test q receipt ep late bare)
  · simpa only [w] using (refunded R hk D Q π Γ Ψ books ahead order shelf seats floor A simple cut o P course scroll chamber hospital load wide test q receipt income ep late extent bare wages)

end YM.Integration.WilsonThermometerAppointedDetector
end
