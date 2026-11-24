import YM.Integration.WilsonThermometerMixedTandemWallet
import YM.Integration.WilsonThermometerMixedOutlet
import YM.Integration.WilsonCenteredIncomeRate

/-! The full enlarged and erased reports on the original two programs fit the same six-fold marker radius. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialAnyRegular
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (hi : m ≤ i) (cut : i < N)
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson : Lesson (N:=N) R hk D Q π Γ hi)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V ι : Type} [DecidableEq V] [Fintype V] {marks : Census V} {X : V → Type}
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

local notation "fine" => Ψ (i+1)
local notation "coarse" => Ψ i
local notation "width" => (fine).p.supportExponent
local notation "level" => (fine).p.B



local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi op lesson ahead actors M order voter
local notation "oldG" => Coat.gStep (fine).beta
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "age" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "θ" => (coarse).p.supportExponent+1+1
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "due" => Invoice.price (coarse).p (fig).mist (order+shelf+1) op.count (θ) (fig).limitC G
local notation "stipend" => (fig).produce (sheet).ratio.count*cost
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G (sheet).ratio.count (fine).p (coarse).p
  (Ω⁻¹*cost) (Ω⁻¹*rent) (Burn.young age k) oldG
local notation "A₁" => Tint.Patrol.report student Y oldG
local notation "w₆" => Stoop.radius w (Ω^6)

theorem original (_way:WayStation R.kit)(cost0:0 ≤ cost)(cheap:cost ≤ 1)(small:rent ≤ 1)
    (T:Oak.Buffered.SuccessStory R hk D Q π Γ Ψ books hi op lesson ahead actors pieces M Z w grades order shelf
      voter rent cost (J:=next) Y) :
    let G₁:=(A₁)
    G₁.E.Paid (w₆) (coarse).p.B ((coarse).p.supportExponent+2) 1 ∧
    (∀j,0<(w₆) j):=by
  intro G₁
  let cash:=T.Waffle
  have pos:=cash.paysAbove
  have low:=cash.cool
  have win:=T.earning.positive
  have rich:stipend ≤ Ω:=by
    apply (mul_le_mul_of_nonneg_right cash.earns cost0).trans
    exact mul_le_of_le_one_right pos.le cheap
  have cap:due*stipend ≤ Ω^2:=by
    rw [pow_two]
    exact (mul_le_mul_of_nonneg_left rich cash.minted.le).trans (mul_le_mul_of_nonneg_right cash.quote pos.le)
  have delivered:Ω⁻¹*rent ≤ 1:=
    (mul_le_mul_of_nonneg_left small (inv_nonneg.mpr pos.le)).trans (by simpa using inv_le_one_of_one_le₀ low)
  have young:Burn.young age k ≤ 1:=by
    apply Real.rpow_le_one_of_one_le_of_nonpos (R.alloy.B.a.fits.delayed _).le
    rw [Burn.sale_eq]
    have h:0 ≤ (Burn.horizon k:ℝ):=Nat.cast_nonneg _
    linarith
  have earned:oldFee ≤ 24*Ω:=by
    apply T.effort.trans
    have sum:Ω⁻¹*rent+Burn.young age k+(fig).fidelity ≤ 3:=by linarith only [delivered,young,cash.tenor.2]
    have bank:0≤8*Ω:=mul_nonneg (by norm_num) pos.le
    exact (mul_le_mul_of_nonneg_left sum bank).trans_eq (by ring)
  have psi:=Scene.Armada.paid student w grades T.earning (coarse).p cash.soon
  have p₅:1 ≤ Ω^5:=one_le_pow₀ low
  have p₆:1 ≤ Ω^6:=one_le_pow₀ low
  have soft:=Stoop.tighten w _ win p₆ psi
  have recent:=Stoop.tighten (Stoop.radius w Ω) _ (fun z=>div_pos (win z) pos) p₅ T.local_
  have same:Stoop.radius (Stoop.radius w Ω) (Ω^5)=w₆:=by ext z;change w z/Ω/Ω^5=w z/Ω^6; rw [div_div,pow_succ];ring
  rw [same] at recent
  have fee:(Ω^6)⁻¹*(due*stipend)+(Ω^5)⁻¹*oldFee≤1:=by
    apply le_trans _ (WilsonThermometerMixedTandemWallet.resize cash.strong cap earned)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity : 0≤3*Ω+Ω^2))
      (inv_nonneg.mpr (pow_nonneg pos.le 5)))
  have joined:=Lamps.loan_monotone _ (Lamps.joinPaid soft recent) fee
  refine ⟨?_,fun j=>div_pos (win j) (pow_pos pos _)⟩
  change (A₁).E.Paid _ _ _ _
  rw [show (coarse).p.supportExponent+2=(θ) by ring]
  exact joined
end YM.Integration.WilsonOriginalAlternativeTrialAnyRegular
end
