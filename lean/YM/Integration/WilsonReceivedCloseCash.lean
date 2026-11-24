import YM.Integration.WilsonReceivedInheritedFee
import YM.Integration.WilsonReceivedCloseInterval
import YM.Integration.WilsonFirstReceivedEarnedFee
import YM.Integration.WilsonOriginalCompensatedTuition
import YM.QuadraticLocal.Union.Return

/-! The old regular price on the original funded post, at the reporter's full
marked radii and the actual fine coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCloseCash
open private scales from YM.QuadraticLocal.Pry
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset
open Filter ConnectedActivityE6
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (hi : m ≤ i) (cut : i < N)
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson : Lesson (N:=N) R hk D Q π Γ hi)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V ι : Type} [Fintype V] [DecidableEq V] {marks : Census V} {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  {passport : Earn.Passport (R.family.side (i+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row passport marks G (Affinity.Wallet actors))
  (w : V → ℝ) (grades : V → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))
variable (cost:ℝ) {old next:Type}(pieces:∀ v,Submodule ℝ (X v))
  (Z:Tint.Incoming passport (Ψ (i+1)) (Affinity.Wallet actors) old marks)
  (rent:ℝ) (Y:Tint.Incoming (passport.coarser (R.family.path.levels.clock.op i per).ratio)
      (Ψ i) (Affinity.Wallet actors) next marks)
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "upper" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G
  (R.family.path.levels.clock.op i per).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*cost) (Ω⁻¹*rent) (Burn.young upper k) (Coat.gStep (Ψ (i+1)).beta)
local notation "received" => Oak.Buffered.SuccessStory R hk D Q π Γ Ψ books hi op lesson ahead
  actors pieces M Z w grades order shelf voter rent cost Y

open Pressure

omit [Fintype V] in
private theorem restore {r : ℝ} (hr : 0 < r) (t : V → ℝ) (s : marks.Mode) :
    Poly.toll t s = r^s.val.card * Poly.toll (Stoop.radius t r) s := by
  have cash : Poly.toll (Stoop.radius t r) s = (r^s.val.card)⁻¹ * Poly.toll t s := by
    unfold Stoop.radius Poly.toll
    simp_rw [div_eq_inv_mul,Finset.prod_mul_distrib,Finset.prod_const,inv_pow]
  rw [cash,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hr.ne'),one_mul]

/-- At one authentic returned post the full original healthy derivative envelope
can be retained separately at each actual mark arity and each original hit site. -/
theorem roster (returned : received) :
    ∃ f : next → ℝ, (∀ a, 0 ≤ f a) ∧
      (∀ a t u, u ∈ Y.old.ground a → (Ψ i).p.supBounds u (Y.old.ground a) (Y.old.nominal t a) (f a)) ∧
      ∀ s : marks.Mode, Ac.Hit Y.old.ground (Ψ i).p.B
        (fun a => if Y.old.mode a=s then Poly.toll w s * f a else 0)
        ((Ψ i).p.supportExponent+1+1) (Ω^s.val.card * oldFee) := by
  obtain ⟨f, fp, stayed, funded⟩ := returned.local_.budget
  refine ⟨f, fp, stayed, ?_⟩
  intro s
  have positive := zero_lt_one.trans_le returned.Waffle.cool
  apply scales Y.old.ground funded
  · intro a
    split
    · exact mul_nonneg (Poly.worth returned.earning.positive s).le (fp a)
    · exact le_rfl
  · intro a
    by_cases has : Y.old.mode a=s
    · simp only [has,if_true]
      rw [restore positive w s, mul_assoc]
    · have g (v : V) : 0 < Stoop.radius w (Ω) v := div_pos (returned.earning.positive v) positive
      simp only [if_neg has]
      exact mul_nonneg (pow_nonneg positive.le _) (mul_nonneg (Poly.worth g _).le (fp a))
  · exact pow_nonneg positive.le _

include cut in
/-- The actual inherited charge at a specified mask, with one common fee for
new truncations. Its exponent is the number of physical marks present there. -/
theorem enrolled (returned : received) (simple : G.Simple) (p : ℕ) (s : marks.Mode)
    (deep : 2*(p+1)+8 ≤ order) (aged : p+4 ≤ 3*k+2) {ε : ℝ} (positive : 0 < ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple op.count p order k deep aged positive ≤ i)
    (incoming : 0 ≤ rent) (u : ℝ) (up : ε*(Coat.gStep (R.family.path.rep N per (i+1)).beta)^p ≤ u) :
    Ω^s.val.card * oldFee + u ≤ (budgetR R i)^(s.val.card+2)*(rent+u) := by
  have orig := WilsonReceivedInheritedFee.original R hk D Q π Γ Ψ books hi cut op lesson ahead
    actors M w grades order shelf voter cost pieces Z rent Y returned simple p deep aged positive opened
  let t := s.val.card
  let c := (Ω)^(op.count-t)
  let fresh := ε*(Coat.gStep (R.family.path.rep N per (i+1)).beta)^p
  have fp : 0 ≤ fresh := mul_nonneg positive.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  have os : 0 < Ω := zero_lt_one.trans_le returned.Waffle.cool
  have cp : 0 < c := pow_pos os _
  have c1 : 1 ≤ c := one_le_pow₀ returned.Waffle.cool
  have limit : t ≤ op.count := returned.earning.quota s
  have split : Ω^op.count=c*Ω^t := by rw [← pow_add]; congr 1; omega
  have raw : Ω^t * oldFee ≤ (8*Ω^t)*rent + fresh := by
    apply le_of_mul_le_mul_left (a:=c)
    · calc
        _ = Ω^op.count * oldFee := by rw [split]; ring
        _ ≤ (8*Ω^op.count)*rent + fresh := orig
        _ ≤ (8*Ω^op.count)*rent + c*fresh := add_le_add le_rfl (le_mul_of_one_le_left fp c1)
        _ = c*((8*Ω^t)*rent+fresh) := by rw [split]; ring
    · exact cp
  have cube : 8 ≤ Ω^2 := by nlinarith only [returned.Waffle.strong,sq_nonneg ((Ω)-4)]
  let T := (budgetR R i)^(t+2)
  have price : 8*(Ω)^t ≤ T := by
    calc
      _ ≤ Ω^2*Ω^t := mul_le_mul_of_nonneg_right cube (pow_nonneg os.le _)
      _ = Ω^(t+2) := by rw [pow_add,mul_comm]
      _ ≤ _ := pow_le_pow_left₀ os.le returned.Beamwork _
  have times : 2 ≤ T := by linarith only [price,one_le_pow₀ (n:=t) returned.Waffle.cool]
  have d := mul_le_mul_of_nonneg_right price incoming
  have new := mul_le_mul_of_nonneg_right times (fp.trans up)
  change Ω^t*oldFee+u ≤ T*(rent+u)
  rw [mul_add]
  linarith only [raw,d,new,up]

end YM.Integration.WilsonReceivedCloseCash
