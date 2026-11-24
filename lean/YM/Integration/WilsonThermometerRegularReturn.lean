import YM.Integration.WilsonOriginalReceivedChain
import YM.Integration.WilsonThermometerTestedReturn

/-! Advance the complete original three-marker offer. The same marked
density, including every scalar probe, re-enters with a paid regular rent. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegularReturn
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

/-- Both marker restoration and regular rent are those of the single returned
post. A previous regular family that vanishes can be issued at any positive
initial tolerance. -/
theorem original (ref : ∀ t : Fin 3, R.family.ref (grade t) ≤ N)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (pass : Pass D Q R.alloy R.kit)
    (scroll : VowsR.LawScroll G φ) (chamber : VowsR.Chamber scroll R.kit D Q books)
    (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J i)
    (load : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (q : ℕ) (deep : 2*q+8 ≤ order) (aged : q+3 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (late : WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ i+1) :
    ∃ h : ℝ, 1 ≤ h ∧ ∃ L : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead disks sectors ages
      order shelf seats i floor (offered R A simple (Nat.lt_of_succ_lt live) o),
      (∀ v, L.w v = P.w v/(funds^6*h)) ∧ L.rent ≤ P.rent+ε*g^q ∧
      (P.rent ≤ ε*g^q → L.rent ≤ 2*ε*g^q) ∧
      h ≤ max 1 (max (QuadraticLocal.Advent.budgetR R i*QuadraticLocal.Advent.budgetR R (i+1)) (P.rent+ε*g^q)) := by
  let g₀ := Coat.gStep (R.family.path.rep N per (i+2)).beta
  have pos : 0 < g₀ := by
    exact ActualRunKernelPackets.regulator_pos R N per (i+2) live
  let b := P.rent+ε*g₀^q
  have positive : 0 < b := add_pos P.active (mul_pos ep (pow_pos pos _))
  obtain ⟨h,C,E,lesson,one,_cap,quote,existsL⟩ := WilsonOriginalReceivedChain.next R hk D Q π Γ Ψ books ahead
    disks sectors ages order shelf seats floor (offered R A simple live o) P course path live pass scroll chamber
    month hospital fits narrow load packed simple q deep aged ep late fired
  have next := existsL (min 1 b) (lt_min zero_lt_one positive) (min_le_left _ _)
  rw [WilsonThermometerTestedReturn.push R A simple live o ref] at next
  obtain ⟨L,_,wallet,_,rent,_,ceiling⟩ := next
  have inv : 0 ≤ h⁻¹ := inv_nonneg.mpr (zero_le_one.trans one)
  have priced : h⁻¹*E ≤ b := (mul_le_mul_of_nonneg_left quote inv).trans
    (mul_le_of_le_one_left positive.le (inv_le_one_of_one_le₀ one))
  have full : L.rent ≤ b := rent.le.trans (max_le priced (min_le_right _ _))
  refine ⟨h,one,L,wallet,full,(fun small => ?_),ceiling⟩
  change L.rent ≤ 2*ε*g₀^q
  dsimp only [b] at full
  linarith only [full,small]
end YM.Integration.WilsonThermometerRegularReturn
end
