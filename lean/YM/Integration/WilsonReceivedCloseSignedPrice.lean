import YM.Integration.WilsonReceivedCloseHistoryPrice
import YM.Integration.WilsonReceivedCloseEndpoint

/-! The last signed physical-to-finite comparison, after all earlier enrolled close prices. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseSignedPrice
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "B" => budgetR R
local notation "g" => regulatorRun R.family N per
local notation "stage" j:max => (B j)^2*(B (j+1))^7

def opening (simple : G.Simple) (degree a q seats : ℕ) {cap η ε : ℝ} (cn : 0 ≤ cap) (loss : 0 < η) (en : 0 ≤ ε) : ℕ :=
  max (WilsonReceivedCloseHistoryPrice.opening R simple degree a q cn loss en)
    (eventually_atTop.mp (WilsonReceivedCloseEndpoint.with_history R simple degree (a+seats+2) q cn loss en)).choose

private theorem stage_one (j : ℕ) : 1 ≤ stage j :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ (budget_pos R)) (one_le_pow₀ (budget_pos R))

private theorem page (i b : ℕ) (ib : i ≤ b) : B i ≤ (stage b)*(∏ j ∈ Ico i b,stage j) := by
  have base (k : ℕ) : B k ≤ stage k := by
    have doubled : B k ≤ (B k)^2 := by
      simpa only [pow_one] using (pow_le_pow_right₀ (budget_pos (i:=k) R) (by norm_num : 1 ≤ 2))
    exact doubled.trans (le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ (budget_pos R)))
  rcases eq_or_lt_of_le ib with eq|lt
  · subst i; simpa using base b
  · have one := one_le_prod (s:=Ico (i+1) b) (fun j _ => stage_one R j)
    have remain := le_mul_of_one_le_right (zero_le_one.trans (stage_one R i)) one
    rw [←insert_Ico_add_one_left_eq_Ico lt,prod_insert (by simp)]
    exact (base i).trans (remain.trans (le_mul_of_one_le_left
      (mul_nonneg (zero_le_one.trans (stage_one R i)) (zero_le_one.trans one)) (stage_one R b)))

include mb in
theorem paid (P₀ : P b mb source)
    (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ) (top : b < N)
    (pass : Pass D Q R.alloy R.kit) (scroll : VowsR.LawScroll G φ)
    (chamber : VowsR.Chamber scroll R.kit D Q books) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (narrow : shelf ≤ R.alloy.B.a.clock.J m)
    (load : seats ≤ Burn.horizon k+2) (packed : order+shelf ≤ Burn.horizon k+2)
    (simple : G.Simple) (q : ℕ) (deep : 2*q+8 ≤ order) (aged : q+3 ≤ 3*k+2)
    {ε : ℝ} (ep : 0 < ε) (unit : ε ≤ 1)
    (late : WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ m+1)
    (test : Wallet actors) (degree a : ℕ) {cap η : ℝ} (cn : 0 ≤ cap) (loss : 0 < η)
    (ready : opening R simple degree a q seats cn loss ep.le ≤ b) (close : PaceR.Close R degree cap m b) :
    ∀ i (ib : i ≤ b) (mi : m ≤ i), ∃ L : P i mi (read i ib),
      WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
        mb source P₀ i mi (read i ib) L ∧ ∀ s : (Stock.census V).Mode, s.val.card ≤ a → ∀ z : ℝ,
        Poly.toll L.w s*z ≤ (8*(Oak.expenseReal R hk D Q π Γ books mi L.op L.lesson ahead order shelf)^L.op.count)*L.rent+ε*(g (i+1))^q →
        Poly.toll P₀.w s*z ≤ (g b)^(-η)*(P₀.rent+2*ε*(3*g b)^q) := by
  intro i ib mi
  obtain ⟨pre,fiscal⟩ := max_le_iff.mp ready
  obtain ⟨_,fore⟩ := max_le_iff.mp pre
  obtain ⟨ahead₁,small⟩ := max_le_iff.mp fore
  have gates := (eventually_atTop.mp (WilsonReceivedCloseReentry.small R simple degree cap)).choose_spec b small m mb close N per
  have bands := (eventually_atTop.mp (WilsonReceivedCloseChainFunding.upper R simple degree cap)).choose_spec b ahead₁ m mb close N per top.le
  have funds := (eventually_atTop.mp (WilsonReceivedCloseEndpoint.with_history R simple degree (a+seats+2) q cn loss ep.le)).choose_spec
    b fiscal m mb close N per top.le i mi ib
  obtain ⟨L,d,one,more,weights,amount,issued,trail⟩ := WilsonReceivedCloseHistory.descent R hk D Q π Γ Ψ books
    ahead actors pieces grades order shelf seats mb source P₀ course path top pass scroll chamber month hospital
    fits narrow load packed simple q deep aged ep unit late test (fun j mj jN => ⟨(bands j mj jN).1,gates j mj jN⟩) i ib mi
  refine ⟨L,trail,?_⟩
  intro s size z measured
  let t := (stage b)*(∏ j ∈ Ico i b,stage j)
  let Ω := Oak.expenseReal R hk D Q π Γ books mi L.op L.lesson ahead order shelf
  let base := ε*(3*g b)^q
  let sum := ∑ j ∈ Ico i b, ε*(g (min N (j+2)))^q
  have t₁ : 1 ≤ t := one_le_mul_of_one_le_of_one_le (stage_one R b) (one_le_prod (fun j _=>stage_one R j))
  have dCap : d ≤ t := more.trans (le_mul_of_one_le_left
    (prod_nonneg (fun j _=>zero_le_one.trans (stage_one R j))) (stage_one R b))
  have O4 : 4 ≤ Ω := MintClock.Page.roofers ..
  have Oi : Ω ≤ t := L.issued.Beamwork.trans (page R i b ib)
  have power : 8*Ω^seats ≤ t^(seats+2) := by
    rw [pow_add,mul_comm (t^seats)]
    exact mul_le_mul (by nlinarith only [O4,Oi,sq_nonneg (t-4)]) (pow_le_pow_left₀ (by linarith) Oi _)
      (pow_nonneg (by linarith) _) (sq_nonneg _)
  have b₀ : 0 ≤ base := mul_nonneg ep.le (pow_nonneg (mul_nonneg (by norm_num) (bands b mb top.le).1.le) _)
  have charge : ε*(g (i+1))^q ≤ base := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (bands (i+1) (by omega) (by omega)).1.le (bands (i+1) (by omega) (by omega)).2 _) ep.le
  have scaled : (8*Ω^L.op.count)*L.rent+ε*(g (i+1))^q ≤ t^(seats+2)*(P₀.rent+base+sum) := by
    rw [L.capacity]
    calc
      _ ≤ t^(seats+2)*(P₀.rent+sum) + t^(seats+2)*base := add_le_add
        (mul_le_mul power amount L.active.le (pow_nonneg (zero_le_one.trans t₁) _))
        (charge.trans (le_mul_of_one_le_left b₀ (one_le_pow₀ t₁)))
      _ = _ := by ring
  have newCash := funds (P₀.rent+base) (add_nonneg P₀.active.le b₀) issued
  have coin : t^(a+seats+2)*(P₀.rent+base+sum) ≤ (g b)^(-η)*(P₀.rent+2*ε*(3*g b)^q) := by
    convert newCash using 1
    · dsimp only [t,sum]
      rw [mul_pow,mul_assoc]; congr 2
      first | exact prod_pow .. | symm; exact prod_pow ..
    · dsimp only [base]; ring
  have fd : 0 < d := zero_lt_one.trans_le one
  have folio : Poly.toll P₀.w s = d^s.val.card*Poly.toll L.w s := by
    unfold Poly.toll
    rw [prod_congr rfl (fun v _ => weights v),prod_div_distrib,prod_const]
    field_simp
  calc
    _ = d^s.val.card*(Poly.toll L.w s*z) := by rw [folio,mul_assoc]
    _ ≤ d^s.val.card*(t^(seats+2)*(P₀.rent+base+sum)) :=
      mul_le_mul_of_nonneg_left (measured.trans scaled) (pow_nonneg fd.le _)
    _ ≤ t^(a+seats+2)*(P₀.rent+base+sum) := by
      rw [←mul_assoc,show a+seats+2=a+(seats+2) by omega,pow_add t a (seats+2)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        ((pow_le_pow_left₀ fd.le dCap _).trans (pow_le_pow_right₀ t₁ size)) (pow_nonneg (zero_le_one.trans t₁) _))
        (by linarith only [amount,L.active,b₀])
    _ ≤ _ := coin

end YM.Integration.WilsonReceivedCloseSignedPrice
