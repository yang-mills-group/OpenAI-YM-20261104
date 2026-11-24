import YM.Integration.WilsonOriginalThermometerFiledCells
import YM.Integration.WilsonOriginalThermometerTopPositions
import YM.Integration.WilsonThermometerCourseHearing

/-! Separated withdrawals on the original top-deposited seven faces. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFundedJoinCells
open Filter Set Finset Wilson Lattice RG Tree Marker Ac QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open FVA1 OriginalForcedAddresses WilsonThermometerCourseIntake
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure Extraction Source ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonReceivedCloseHistory
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonThermometerCourseHearing WilsonSeparatedOriginalThermometerCells
open WilsonOriginalThermometerFineHarvest WilsonOriginalThermometerFineCover WilsonOriginalThermometerFiledCells
open scoped BigOperators Topology ContDiff

variable {G : Gauge} (R : Run G) (simple : G.Simple)
    (Φ : Test 3) (admit : tsupport Φ ⊆ conf 3) (K H q : ℕ)

private abbrev cut := WilsonOriginalThermometerFiledCells.original R simple Φ admit K H q

noncomputable def period : ℕ := (cut R simple Φ admit K H q).choose
noncomputable def age : ℕ :=
  (eventually_atTop.1 (cut R simple Φ admit K H q).choose_spec).choose

variable (A : Group R.family 6) {m b per k : ℕ}
    (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
    (ahead : Mentor.Forecast D R.rolls Q φ books)
    (order shelf seats : ℕ) (mb : m ≤ b) (o : Positions (Fin 3) (R.family.side (b+1) per))
local notation "ages" => (fun v : Fin 3 => (grade v).val)
local notation "panel" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self b) o
variable (P₀ : WilsonOriginalReceivedChain.Post (N:=b+1) R hk D Q π Γ Ψ books ahead disks sectors (fun v : Fin 3 => (grade v).val) order shelf seats b mb (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self b) o)) (located : P₀.passport=Earn.Passport.point o.origin)
    {i : ℕ} {floor : m ≤ i}
    {y : Wallet disks → Config G (R.family.side (i+1) per) → Poly (Stock.census (Fin 3))}
    {P : WilsonOriginalReceivedChain.Post (N:=b+1) R hk D Q π Γ Ψ books ahead disks sectors ages
      order shelf seats i floor y}
    (chain : Trail R hk D Q π Γ Ψ books ahead disks sectors ages order shelf seats mb (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self b) o) P₀ i floor y P)
    (course : Concourse R.alloy R.kit R.T π Γ m (b+1) per k Ψ)

include course located chain in
/-- The support condition for native first withdrawal follows on every nonzero integrated
cell of the measured finite program, at every date of its actual dated enrollment. -/
theorem original (young : age R simple Φ admit K H q ≤ m) (room : period R simple Φ admit K H q ≤ per)
    (r : ℝ) (rp : 0 < r) (cap : r ≤ 1) (span : R.family.S.a m*(RG16.Lambda R.family.path.levels m)^4 ≤ r)
    (occupied : weight Φ (positions (R:=R) r (b+1,per)) o.origin ≠ 0) (v : Fin 3) :
    ∀ t, first v t → ∃ a ∈ t.val, ∃ w ∈ t.val,
      depth R (bill K H q m (i+1)) m (i+1)*(4*(Ψ (i+1)).p.B+2)+2*(Ψ (i+1)).p.B ≤
        separation (P.passport.origin a) (P.passport.origin w) := by
  obtain ⟨top,places⟩ := Trail.fromTop R hk D Q π Γ Ψ books ahead disks sectors ages order shelf seats
    mb (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self b) o) P₀ chain o.origin located
  obtain ⟨U,_,_⟩ := (course.2 i floor top).earns
  exact (eventually_atTop.1 (cut R simple Φ admit K H q).choose_spec).choose_spec m young per room
    (b+1) i (floor.trans (Nat.le_succ i)) top r rp cap span o.origin occupied (Ψ (i+1)) U
    P.passport places v

end YM.Integration.WilsonThermometerFundedJoinCells
