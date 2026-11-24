import YM.Integration.WilsonReceivedFirstTrace

/-! A priced first-join link of the actual registered trajectory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedFirstTrace
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)

variable (W : Registration (m:=m) (N:=N) (k:=k) R D Q π Γ Ψ books ahead actors shelf seats)
local notation "carrier" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y


variable {j : ℕ} (floor : m ≤ j)
  (y : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V))
  (U : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) (floor.trans (Nat.le_succ j)) y) (count : Countable U.inputIndex) (cut : j+1<N)

local notation "actual" => install R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W U count cut
local notation "earlier" => (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (y x))
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) U.op U.lesson ahead order shelf
local notation "B" => budgetR R

/-- The fixed appointment keeps the selected old hard gallery inside its actual filed input. -/
structure Receipt (δ h C E τ : ℝ) (L : carrier j floor earlier) : Prop where
  counted : Countable L.inputIndex
  positive : 1 ≤ h
  credit : C ≤ B (j+1)
  available : E ≤ U.rent+δ
  ceiling : h ≤ max 1 (max (B j*B (j+1)) (U.rent+δ))
  cost : L.cost = h⁻¹*C
  rent : L.rent = max (h⁻¹*E) τ
  wages : ∀ v, L.w v=U.w v/(Ω^6*h)
  one : 1 ≤ Ω^6*h
  price : Ω^6*h ≤ (B j)^2*(B (j+1))^7
  received : Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor y actual L

local notation "g" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta

theorem issued (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
    (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (packed : order+shelf ≤ Burn.horizon k+2)
    (q : ℕ) (deep : 2*q+8 ≤ order) (aged : q+3 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)
    (late : WilsonReceivedMeasuredStampPrice.opening R W.simple q order k deep aged ep ≤ j+1)
    (room : U.rent+ε*g^q ≤ 2) :
    ∃ h C E : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∃ L : carrier j floor earlier,
      Receipt R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W floor y U count cut
        (ε*g^q) h C E τ L := by
  letI : Countable (actual).inputIndex := count
  obtain ⟨h,C,E,_,one,credit,income,next⟩ :=
    WilsonOriginalReceivedChain.next_filed_counted R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      floor y actual W.course path cut pass W.scroll W.chamber month W.hospital fits
      (W.narrow.trans (R.alloy.B.a.fits.mono floor)) W.load packed W.simple q deep aged ep late W.test
  refine ⟨h,C,E,fun τ hp hu => ?_⟩
  obtain ⟨L,_,wages,cost,rent,_,ceiling,paid,counted⟩ := next τ hp hu
  have b : 2 ≤ B j := (by norm_num : (2:ℝ)≤4).trans
    ((MintClock.Page.roofers ..).trans L.issued.Beamwork)
  have d : 1 ≤ B (j+1) := budget_pos R
  have Ωp : 1 ≤ Ω := U.issued.Waffle.cool
  have face : B j≤B j*B (j+1) := le_mul_of_one_le_right (by linarith only [b]) d
  have enough : h≤B j*B (j+1) := ceiling.trans (max_le (by linarith only [b,face])
    (max_le le_rfl (room.trans (b.trans face))))
  have scale : Ω^6*h ≤ (B j)^2*(B (j+1))^7 := by
    calc
      _ ≤ (B (j+1))^6*(B j*B (j+1)) :=
        mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans Ωp) U.issued.Beamwork _) enough
          (zero_le_one.trans one) (pow_nonneg (zero_le_one.trans d) _)
      _ = B j*(B (j+1))^7 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by simpa only [pow_two] using (le_mul_of_one_le_right (by linarith only [b] : 0≤B j)
          (by linarith only [b] : 1≤B j))) (pow_nonneg (zero_le_one.trans d) _)
  exact ⟨L,counted,one,credit,income,ceiling,cost,rent,wages,
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ Ωp) one,scale,paid⟩

end YM.Integration.WilsonReceivedFirstTrace
