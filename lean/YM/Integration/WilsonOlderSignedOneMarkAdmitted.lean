import YM.Integration.WilsonOlderFreshIssuedIntake
import YM.QuadraticLocal.Tariff.Measure

/-! Integrability of the actual uncut one-source polynomial on the elected prior. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkAdmitted
open MeasureTheory
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org 
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))

local notation "post" F:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades order shelf seats i floor F
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades order shelf seats i floor physical)
local instance : Countable P.modelIndex := P.modelCount
local notation "fine" => Ψ (i+1)
local notation "gf" => Coat.gStep (fine).beta
local notation "κ" => forcedDivisor R.family (i+1)
local notation "βhat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "fresh" => (fun (x : Wallet actors) (U : Config G (R.family.side (i+1) per)) =>
  ((fine).eval U : ℂ) • Poly.pass (Spill.Foundry.uncut P.model gf x U))
local notation "pupil" S:max => Oak.student (n:=per) R hk D Q π Γ books floor (S).op (S).lesson ahead
  actors (S).model order (S).voter


private theorem less {S : Type} [Fintype S] [DecidableEq S] {c : Side} {p : BudgetPoint}
    {D : Census S} {r s b : ℝ} {I T : Type} {o : S → Site c} {B : ℕ}
    {w : S→ℝ} {L : Lamps T I G p o D} (hp : ∀ i,0<w i) (inc : L.Paid w B r b)
    (size : s≤r) : L.Paid w B s b := by
  obtain ⟨f,positive,values,hit⟩:=inc.budget
  refine ⟨f,positive,values,fun x=>Push.AbsoluteSums.budget_mono (hit x) ?_ ?_⟩
  · intro i
    split
    · exact mul_nonneg (mul_nonneg (Poly.worth hp _).le (positive _)) (Real.exp_nonneg _)
    · exact le_rfl
  · intro i
    split
    · exact mul_le_mul_of_nonneg_left (Real.exp_monotone
        (mul_le_mul_of_nonneg_right size (by positivity)))
        (mul_nonneg (Poly.worth hp _).le (positive _))
    · exact le_rfl

include course in
theorem original (cut : i<N) (scroll : VowsR.LawScroll G φ)
    (chamber : VowsR.Chamber scroll R.kit D Q books)
    (warm : Spill.Raffle.Warm G D R.alloy.delay φ)
    (top : Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (fits : order ≤ Burn.horizon k+1) (load : seats ≤ Burn.horizon k+2)
    (packed : order+shelf ≤ Burn.horizon k+2)
    (d : ℕ) (space : Sycamore.Boot.need d (⟨order,seats,shelf,load,fits,packed⟩ : Syl.School k)
      ≤ R.alloy.B.a.clock.J (i+1))
    (x : Wallet actors) : Integrable (fresh x) (prior G _) := by
  let school : Syl.School k := ⟨order,seats,shelf,load,fits,packed⟩
  have unit : P.cost ≤ 1 := P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool)
  have stock : Scene.Armada P.model P.w grades
      (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) 1
      school.order school.pieces school.horizon := by
    change Scene.Armada _ _ _ _ 1 order seats shelf
    simpa only [P.capacity] using P.salary.higher unit
  obtain ⟨Z,entry⟩ := Sycamore.Boot.launching R hk D Q π Γ Ψ course scroll books chamber
    (floor.trans i.le_succ) cut actors pieces P.w grades school P.model stock P.tests warm top d space

  let pic := Tint.Patrol.picture P.model Z
  have positive:=P.salary.positive
  have old := Spill.Foundry.empty_lit (fine) Z (fine).p.supportExponent (fine).p.B (w:=P.w)
  have soft := Lamps.joinPaid (less positive entry.funding (by linarith : (fine).p.supportExponent≤(fine).p.supportExponent+1)) old
  have funds : pic.Pays P.w (fine).p.supportExponent _ _ := ⟨soft,entry.crown⟩
  have admitted := QuadraticLocal.Tariff.integrable (Stock.census V) _ P.w positive pic x funds
    (fine).p.exponent_pos.le (course.1.walk (i+1) (floor.trans i.le_succ) cut).truep.valid
  convert admitted using 1
  funext U
  exact (entry.face x U).2.2.symm

end YM.Integration.WilsonOlderSignedOneMarkAdmitted
