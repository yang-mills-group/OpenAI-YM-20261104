import YM.Integration.WilsonReceivedCenteredFaces
import YM.Comparison.RG02.Assembly.Core
import YM.Comparison.RG02.Order.Pay

/-! Truncate the total coupling grade of the full pair on the normalized finite Wick program. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCenteredGrade
open Finset Marker Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open scoped Classical BigOperators

section Elementary
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

def remainder (w : V → ℝ) (x : Grade R r) (z : ℝ) :=
  subtotal w r z (logSeries (Fintype.card V+r) (render (ratio x)))

theorem finite (x : Grade R r) (g : ℂ) (w : V → ℝ) (positive : ∀ i, 0<w i)
    (unit : UnitLeading x) (sym : Symmetric x) (z : ℝ) (radius : ‖g‖≤z)
    (a b c : V) (s : R.Mode) (different : a≠b) (pair : s.val={a,b}) :
    let Z := value g (ratio x)
    let T := value g (logMarked x)
    let cost := fun t => ‖g‖^(r+1)*remainder w x z / Poly.toll w t
    let axis := R.fire
    ‖(Z.part s - Z.part (axis c)) -
      (T.part s - T.part (axis c) + T.part (axis a)*T.part (axis b))‖ ≤
      cost s + cost (axis c) + cost (axis a)*‖Z.part (axis b)‖ +
        ‖T.part (axis a)‖*cost (axis b) := by
  intro Z T cost axis
  have quiet := leading_trunc_value (ratio_pure unit) g
  apply WilsonReceivedCenteredMoment.priced Z T quiet a b c s different pair cost
  intro t _
  let polynomial := logSeries (Fintype.card V+r) (render (ratio x))
  have defect : logTo (Fintype.card V) Z - T = omitted r g polynomial := by
    rw [← log_to Z quiet (Fintype.card V) (fun _ => Finset.card_le_univ _)]
    exact sub_eq_iff_eq_add'.mpr (log_mark_defect unit sym g (Fintype.card V) (fun _ => Finset.card_le_univ _))
  rw [defect]
  apply (le_div_iff₀ (Poly.worth positive t)).mpr
  rw [mul_comm]
  exact (Poly.member positive t _).trans (tail_bound w positive r z polynomial g radius)

end Elementary

private theorem join (y z target : ℂ) (py pz : ℝ)
    (hy : ‖y-target‖ ≤ py) (hz : ‖z-target‖ ≤ pz) : ‖y-z‖ ≤ py+pz := by
  calc
    ‖y-z‖ = ‖(y-target)-(z-target)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hy hz)

open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) {m N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats i : ℕ) (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))

local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
variable (simple : G.Simple)
  (paid : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
  (q : ℕ) (deep : 2*(q+1)+8 ≤ order) (aged : q+4 ≤ 3*k+2) {ε : ℝ} (ep : 0<ε)

theorem original (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (law : VowsR.LawScroll G φ) (enrolled : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay) (live : i<N) (fit : k≤R.alloy.B.a.clock.J i)
    (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical)
    (late : WilsonReceivedCenteredFaces.Mature R D grades order shelf seats simple paid q deep aged ep i)
    (a b c : V) (s : (Stock.census V).Mode) (distant : a≠b) (pair : s.val={a,b})
    (x : Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices) :
    let Y := (((Ψ i).eval 1:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i (physical x) 1
    let bank := Air.craft P.model (fun j => (P.model j).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
    let program := (RunFormalChain.fromRun R).step N i per live
    let W := Bulk.Fk program F tag bank 0 order
    let Z := Order.value (g:ℂ) (Order.ratio W)
    let T := Order.value (g:ℂ) (Order.logMarked W)
    let axis := (Stock.census V).fire
    let fee := fun (C : ℝ) (other : Marker.Poly (Stock.census V)) =>
      let cost := fun t => C/(Poly.toll P.w t)
      cost s + cost (axis c) + cost (axis a)*‖other.part (axis b)‖ + ‖T.part (axis a)‖*cost (axis b)
    ‖(Y.part s - Y.part (axis c)) - (Z.part s - Z.part (axis c))‖ ≤
      fee (8*(budgetR R i)^seats*P.rent+ε*g^q) Y +
        fee (‖(g:ℂ)‖^(order+1)*remainder P.w W ‖(g:ℂ)‖) Z := by
  intro Y bank program W Z T axis fee
  letI := P.modelCount
  have originalPaid := WilsonReceivedCenteredFaces.original R hk D Q π Γ Ψ books ahead actors pieces
    grades order shelf seats i floor physical simple paid q deep aged ep course law enrolled fund live fit
    P late a b c s distant pair x F tag
  have unit : Order.UnitLeading W := Assembly.prescription_unit ..
  have sym : Order.Symmetric W := Assembly.prescription_sym (hv := program.positive F tag) ..
  have finitePaid := finite W (g:ℂ) P.w P.salary.positive unit sym ‖(g:ℂ)‖ le_rfl a b c s distant pair
  let C := T.part s - T.part (axis c) + T.part (axis a)*T.part (axis b)
  exact join (Y.part s-Y.part (axis c)) (Z.part s-Z.part (axis c)) C
    (fee (8*(budgetR R i)^seats*P.rent+ε*g^q) Y)
    (fee (‖(g:ℂ)‖^(order+1)*remainder P.w W ‖(g:ℂ)‖) Z) originalPaid finitePaid

end YM.Integration.WilsonReceivedCenteredGrade

