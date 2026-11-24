import YM.Integration.WilsonThermometerRegularReturn
import YM.Integration.WilsonLocalCompactRichPortUnits

/-! Advance the complete original three-marker offer. The same marked
density, including every scalar probe, re-enters with a paid regular rent. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFirstRent
open Finset Filter Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler AllOrder.Transit.WheelP
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure OriginalForcedAddresses MergeProof MergeProof.East
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6
open IterationFour Push.AbsoluteSums.Animals Extra.Trajectories FVA1
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonThermometerCourseIntake WilsonThermometerCourseHearing
open scoped Classical BigOperators Topology
local notation "J" => Stock.census (Fin 3)

/-- Stage at which the actual allowance covers the restored analytic wallet
and the true upper-date currency simultaneously for all periods. -/
def opening {G : Gauge} (R : Run G) (simple : G.Simple) (q order k seats : ℕ)
    (deep : 2*(q+1)+8 ≤ order) (aged : (q+1)+3 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε) : ℕ :=
  max (WilsonReceivedMeasuredStampPrice.opening R simple (q+1) order k deep aged zero_lt_one)
    (eventually_atTop.mp (WilsonMovingMentorPageCoupling.repaid R simple seats q
      (div_pos ep (by positivity : 0 < 16*(2:ℝ)^(q+1))))).choose

variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
    {N i per m k : ℕ} (live : i+1 < N) (o : Positions (Fin 3) (R.family.side N per))

variable (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ books)
    (order shelf seats : ℕ) (floor : m ≤ i)
local notation "ages" => (fun j : Fin 3 => (grade j).val)
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead disks sectors ages
  order shelf seats (i+1) (floor.trans (Nat.le_succ i)) (offered R A simple live o))
local notation "funds" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ i)) P.op P.lesson ahead order shelf
local notation "g" => Coat.gStep (R.family.path.rep N per (i+2)).beta

theorem original (ref : ∀ t : Fin 3, R.family.ref (grade t) ≤ N)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (pass : Pass D Q R.alloy R.kit)
    (scroll : VowsR.LawScroll G φ) (chamber : VowsR.Chamber scroll R.kit D Q books)
    (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J i)
    (load : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (q : ℕ) (deep : 2*(q+1)+8 ≤ order) (aged : (q+1)+3 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (late : opening R simple q order k seats deep aged ep ≤ i) (bare : P.rent ≤ (g)^(q+1)) :
    ∃ h : ℝ, 1 ≤ h ∧ ∃ L : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead disks sectors ages
      order shelf seats i floor (offered R A simple (Nat.lt_of_succ_lt live) o),
      (∀ v, L.w v = P.w v/(funds^6*h)) ∧
      (8*(Oak.expenseReal R hk D Q π Γ books floor L.op L.lesson ahead order shelf)^seats)*L.rent ≤
        ε*(Coat.gStep (R.family.path.rep N per (i+1)).beta)^q ∧
      h ≤ max 1 (max (budgetR R i*budgetR R (i+1)) (P.rent+(g)^(q+1))) := by
  let gs := Coat.gStep (R.family.path.rep N per (i+1)).beta
  let gt := Coat.gStep (R.family.path.rep N per (i+2)).beta
  let c := 16*(2:ℝ)^(q+1)
  have cp : 0 < c := by dsimp [c]; positivity
  let δ := ε/c
  have dp : 0 < δ := div_pos ep cp
  obtain ⟨h,h₁,L,wallet,_,rent,ceiling⟩ :=
    WilsonThermometerRegularReturn.original R A simple live o hk D Q π Γ Ψ books ahead
      order shelf seats floor P ref course path pass scroll chamber month hospital fits narrow load packed
      (q+1) deep aged zero_lt_one ((le_max_left ..).trans (late.trans (Nat.le_succ i)))
  let Ω := Oak.expenseReal R hk D Q π Γ books floor L.op L.lesson ahead order shelf
  have Ω0 : 0 ≤ Ω := zero_le_one.trans L.issued.Waffle.cool
  have many := (eventually_atTop.mp (WilsonMovingMentorPageCoupling.repaid R simple seats q dp)).choose_spec
    i ((le_max_right ..).trans late) Ω Ω0 (L.issued.Beamwork.trans (min_le_right ..)) N per (by omega)
  change Ω^seats*gs^(q+1) ≤ δ*gs^q at many
  have right : gt ≤ 2*gs := WilsonLocalCompactRichPortUnits.compared R simple
    (show i+1 ≤ i+2 by omega) (show i+2 ≤ N by omega) per
  have gt0 : 0 ≤ gt := (ActualRunKernelPackets.regulator_pos R N per (i+2) live).le
  have paid : L.rent ≤ 2*gt^(q+1) := by simpa only [one_mul,mul_one] using rent (by simpa only [one_mul] using bare)
  refine ⟨h,h₁,L,wallet,?_,by simpa only [one_mul] using ceiling⟩
  change (8*Ω^seats)*L.rent ≤ ε*gs^q
  have scale : c*δ=ε := by simp [δ,div_eq_mul_inv,cp.ne',mul_left_comm]
  calc
    _ ≤ (8*Ω^seats)*(2*gt^(q+1)) := mul_le_mul_of_nonneg_left paid (by positivity)
    _ ≤ (8*Ω^seats)*(2*(2*gs)^(q+1)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ gt0 right _) (by norm_num)) (by positivity)
    _ = c*(Ω^seats*gs^(q+1)) := by dsimp only [c];rw [mul_pow];ring
    _ ≤ c*(δ*gs^q) := mul_le_mul_of_nonneg_left many cp.le
    _ = _ := by rw [←mul_assoc,scale]

end YM.Integration.WilsonThermometerFirstRent
end
