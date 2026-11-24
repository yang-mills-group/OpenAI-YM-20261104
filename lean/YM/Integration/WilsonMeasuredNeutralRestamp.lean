import YM.Integration.WilsonMeasuredNeutralFiledStock
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredNeutralRestamp
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Pert.Asymptotics
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6 WilsonOriginalReceivedChain
open WilsonMeasuredNeutralFiledStock
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {m j N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  (actors : Unit→ Set ℂ) (pieces : Unit→ Submodule ℝ ℂ)
  (order shelf seats : ℕ) (floor : m ≤ j)
  (physical : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census Unit))
local notation "grades" => (fun _:Unit=>(4:ℕ))
local notation "hi" => floor.trans (Nat.le_succ j)
local notation "next" => (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (physical x))
local notation "Upper" => Post (V:=Unit) (X:=fun _:Unit=>ℂ) (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats (j+1) hi physical
local notation "Lower" => Post (V:=Unit) (X:=fun _:Unit=>ℂ) (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j floor next
variable (P:Post (V:=Unit) (X:=fun _:Unit=>ℂ) (N:=N) R hk D Q π Γ Ψ books ahead actors pieces
  (fun _:Unit=>(4:ℕ)) order shelf seats (j+1) (floor.trans (Nat.le_succ j)) physical)
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "g" => Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
local notation "g₁" => regulatorRun R.family N per (j+1)
local notation "heat" => R.alloy.B.a.clock.hatBeta ((j+1)+1)
local notation "office" => Filed (V:=Unit) (X:=fun _:Unit=>ℂ) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor physical P
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "B" => (Ψ (j+1)).p
local notation "w*" n:max => (fun _:Unit=>g₁^12/n)

/-- The one original funded Walk stamps both complete enrolled inventories and the
independent model.  All three are affordable at the newly posted one-colour radius. -/
theorem original (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path:PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (cut:j+1<N)
    (pass:Pass D Q R.alloy R.kit) (scroll:VowsR.LawScroll G φ)
    (chamber:VowsR.Chamber scroll R.kit D Q books) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (way:WayStation R.kit) (simple:G.Simple)
    (fits:order≤Burn.horizon k+1) (narrow:shelf≤R.alloy.B.a.clock.J j)
    (load:seats≤Burn.horizon k+2) (packed:order+shelf≤Burn.horizon k+2)
    (q:ℕ) (deep:2*q+8≤order) (aged:q+3≤3*k+2)
    {ε:ℝ} (ep:0<ε) (light:ε*g^q≤1)
    (late:WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep≤j+1)
    (fiscal:WilsonMeasuredSemesterSubpower.onset R 6 zero_lt_one≤j+1)
    (threshold:WilsonMeasuredNeutralFiledStock.onset R simple≤j+1)
    (hardOrder:q+6*seats≤R.alloy.B.a.clock.J (j+1))
    (test:Wallet actors) (n:ℝ) (np:0<n) (ticket:(P.w ())⁻¹≤2*heat*n):
    ∃F:Lower, Stocked R hk D Q π Γ Ψ books ahead actors pieces order shelf seats floor physical P F n (P.rent+ε*g^q) q ∧
      F.rent≤P.rent+ε*g^q ∧
      ∃h C E:ℝ, 1≤h ∧ C≤budgetR R (j+1) ∧ E≤P.rent+ε*g^q ∧
        h ≤ max 1 (max (budgetR R j*budgetR R (j+1)) (P.rent+ε*g^q)) ∧
        (∀v,F.w v=P.w v/(Ω^6*h)) ∧ F.cost=h⁻¹*C :=by
  obtain ⟨h,C,E,_,one,cap,service,price⟩:=WilsonOriginalReceivedChain.next_filed
    (V:=Unit) (X:=fun _:Unit=>ℂ) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
    floor physical P course path cut pass scroll chamber month hospital fits narrow load packed simple
    q deep aged ep late test
  have non:0≤ε*g^q:=mul_nonneg ep.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  have budget:0<P.rent+ε*g^q:=add_pos_of_pos_of_nonneg P.active non
  let τ:=min 1 (P.rent+ε*g^q)
  obtain ⟨F,_,weight,stock,rent,_,ceiling,registered⟩:=price τ (lt_min zero_lt_one budget) (min_le_left ..)
  have hp:0<h:=zero_lt_one.trans_le one
  have small:F.rent≤P.rent+ε*g^q:=by
    rw [rent]
    apply max_le _ (min_le_right ..)
    calc
      _ ≤ h⁻¹*(P.rent+ε*g^q):=mul_le_mul_of_nonneg_left service (inv_nonneg.mpr hp.le)
      _ ≤ 1*(P.rent+ε*g^q):=mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ one) budget.le
      _=P.rent+ε*g^q:=one_mul _
  have fee:=WilsonMeasuredSemesterSubpower.charged (V:=Unit) (X:=fun _:Unit=>ℂ) R hk D Q π Γ Ψ course books hi cut
    ahead actors pieces grades order shelf seats physical P 6 zero_lt_one fiscal pass hospital
    (narrow.trans (R.alloy.B.a.fits.mono (Nat.le_succ j))) (P.capacity.trans_le load)
  rw [Real.rpow_one] at fee
  exact ⟨F,WilsonMeasuredNeutralFiledStock.received R hk D Q π Γ Ψ books ahead actors pieces order shelf seats
    floor physical P F registered course way simple cut n np ticket fee threshold q hardOrder
    (by linarith only [P.small,light]) one ceiling weight small,
    small,h,C,E,one,cap,service,ceiling,weight,stock⟩

end YM.Integration.WilsonMeasuredNeutralRestamp
end
