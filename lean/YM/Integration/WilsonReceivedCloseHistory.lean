import YM.Integration.WilsonOriginalReceivedFiledChain
import YM.Integration.WilsonReceivedCloseChainFunding
import YM.MergeProof.South.Window

/-! Finite chronological descent of an actual paid Wilson post, including its original hard family. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseHistory
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

def history (i : ℕ) (ib : i ≤ b) (x : Wallet actors) :
    Config G (R.family.side (i+1) per) → Poly (Stock.census V) :=
  gust R.family.path N per (b+1) (source x) (i+1) (Nat.succ_le_succ ib)

local notation "read" i:max ib:max => history (N:=N) R actors source i ib

omit [(v : V) → Module ℝ (X v)] [(v : V) → AddCommGroup (X v)] in
theorem head : read b le_rfl = source := by funext x; exact gust_base ..

omit [(v : V) → Module ℝ (X v)] [(v : V) → AddCommGroup (X v)] in
theorem adjacent {j : ℕ} (jb : j < b) :
    (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) ((read (j+1) jb) x)) =
      read j jb.le := by
  funext x
  unfold history
  rw [gust_step R.family.path N per (b+1) (source x) (Nat.succ_lt_succ jb)]
  rfl

local notation "P" i:max mi:max ib:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i mi (read i ib)
local notation "B" => budgetR R
local notation "g" => regulatorRun R.family N per
local notation "stage" j:max => (B j)^2*(B (j+1))^7
local notation "Σw" i:max => ∏ j ∈ Ico i b, stage j
local notation "carrier" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y

/-- Each earlier post reads the previous independently filed model and carries its entire signed input. -/
inductive Trail (P₀ : carrier b mb source) : (i : ℕ) → (floor : m ≤ i) →
    (y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)) →
    carrier i floor y → Prop
  | start : Trail P₀ b mb source P₀
  | step {j : ℕ} {floor : m ≤ j}
      {y : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V)}
      {U : carrier (j+1) (floor.trans (Nat.le_succ j)) y}
      {L : carrier j floor (fun x : Wallet actors => LocalComparison.actualPush R.family N per (j+1) (y x))}
      (before : Trail P₀ (j+1) (floor.trans (Nat.le_succ j)) y U)
      (after : Filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats floor y U L)
      (factor : ℝ) (one : 1 ≤ factor) (paid : factor ≤ stage j)
      (moved : ∀v, L.w v = U.w v/factor) :
      Trail P₀ j floor _ L

local notation "trail" p:max i:max f:max y:max l:max =>
  Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source p i f y l

include mb in
/-- Each link is the actual issued success of its predecessor on the same funded course.
All old faces travel inside the complete original polynomial. -/
theorem descent (P₀ : carrier b mb source)
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
    (test : Wallet actors) (small : ∀ j, m ≤ j → j ≤ N → 0 < g j ∧ g j ≤ 1) :
    ∀ i (ib : i ≤ b) (mi : m ≤ i), ∃ (Pᵢ : P i mi ib) (d : ℝ),
      1 ≤ d ∧ d ≤ Σw i ∧ (∀v,Pᵢ.w v=P₀.w v/d) ∧
      Pᵢ.rent ≤ P₀.rent+∑j ∈ Ico i b, ε*(g (min N (j+2)))^q ∧
      (∀j ∈ Ico i b,2 ≤ B j) ∧ trail P₀ i mi (read i ib) Pᵢ := by
  intro i ib
  induction ib using Nat.decreasingInduction with
  | self =>
    intro mi
    rw [head (N:=N) R actors source]
    refine ⟨P₀,1,le_rfl,?_,?_,?_,?_,Trail.start⟩ <;> simp
  | of_succ j jb ih =>
    intro mj
    obtain ⟨U,d,one,more,wallet,bill,old,traced⟩ := ih (mj.trans (Nat.le_succ j))
    have gate := small (j+2) (by omega) (by omega)
    let δ := ε*(g (j+2))^q
    have δp : 0 < δ := mul_pos ep (pow_pos gate.1 _)
    have δmax : δ ≤ 1 := mul_le_one₀ unit (pow_nonneg gate.1.le _) (pow_le_one₀ gate.1.le gate.2)
    obtain ⟨h,C,E,lesson,h₁,_,r,returns⟩ :=
      WilsonOriginalReceivedChain.next_filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mj
      (read (j+1) jb) U course path (by omega) pass scroll chamber month hospital fits
      (narrow.trans (R.alloy.B.a.fits.mono mj)) load packed simple q deep aged ep (by omega) test
    obtain ⟨L,_,wage,_,rent,_,hpaid,entry⟩ := returns δ δp δmax
    have prev : m ≤ j+1 := mj.trans (Nat.le_succ j)
    let Ω := Oak.expenseReal R hk D Q π Γ books prev U.op U.lesson ahead order shelf
    let Δ := Oak.expenseReal R hk D Q π Γ books mj L.op L.lesson ahead order shelf
    have O4 : 4 ≤ Ω := MintClock.Page.roofers ..
    have D4 : 4 ≤ Δ := MintClock.Page.roofers ..
    have upper : Ω ≤ B (j+1) := U.issued.Beamwork
    have lower : Δ ≤ B j := L.issued.Beamwork
    have B₁ : 2 ≤ B j := by linarith only [lower,D4]
    have BB : 2 ≤ (B j)*(B (j+1)) :=
      (le_mul_of_one_le_right (zero_le_one.trans (budget_pos _)) (budget_pos (i:=j+1) R)).trans' B₁
    change h ≤ max 1 (max (B j*B (j+1)) (U.rent+δ)) at hpaid
    have room : h ≤ B j*B (j+1) := hpaid.trans (max_le (by linarith only [BB]) (max_le le_rfl
      (by linarith only [U.small,δmax,BB])))
    have positive : 1 ≤ Ω^6*h := one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by linarith only [O4])) h₁
    have invoice : Ω^6*h ≤ stage j := by
      calc
        _ ≤ (B (j+1))^6*(B j*B (j+1)) := mul_le_mul (pow_le_pow_left₀ (by linarith only [O4]) upper _) room
          (zero_le_one.trans h₁) (pow_nonneg (zero_le_one.trans (budget_pos R)) _)
        _ = (B j)*(B (j+1))^7 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by simpa using (pow_le_pow_right₀ (budget_pos (i:=j) R) (by norm_num : 1 ≤ 2)))
          (pow_nonneg (zero_le_one.trans (budget_pos R)) _)
    change E ≤ U.rent+δ at r
    have age : L.rent ≤ U.rent+δ := by
      rw [rent]
      apply max_le
      · exact (mul_le_mul_of_nonneg_left r (inv_nonneg.mpr (zero_le_one.trans h₁))).trans
          (mul_le_of_le_one_left (U.active.le.trans (le_add_of_nonneg_right δp.le))
            (inv_le_one_of_one_le₀ h₁))
      · exact le_add_of_nonneg_left U.active.le
    rw [←adjacent (N:=N) R actors source jb]
    refine ⟨L,(Ω^6*h)*d,one_le_mul_of_one_le_of_one_le positive one,?_,?_,?_,?_,Trail.step traced entry (Ω^6*h) positive invoice wage⟩
    · rw [←insert_Ico_add_one_left_eq_Ico jb,prod_insert (by simp)]
      exact mul_le_mul invoice more (zero_le_one.trans one) (mul_nonneg
        (pow_nonneg (zero_le_one.trans (budget_pos R)) _) (pow_nonneg (zero_le_one.trans (budget_pos R)) _))
    · intro v
      rw [wage v,wallet v,div_div,mul_comm d]
    · rw [←insert_Ico_add_one_left_eq_Ico jb,sum_insert (by simp),min_eq_right (by omega)]
      dsimp only [δ] at age
      linarith only [age,bill]
    · intro z hz
      rcases eq_or_lt_of_le (mem_Ico.mp hz).1 with eq|more
      · simpa only [←eq] using B₁
      · exact old z (mem_Ico.mpr ⟨more,(mem_Ico.mp hz).2⟩)

/-- The physical weights on the actual filed post, uniformly over every occupied face. -/
theorem Trail.wallet (P₀ : carrier b mb source) {i : ℕ} {mi : m ≤ i}
    {y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {L : carrier i mi y} (invoice : trail P₀ i mi y L) :
    i ≤ b ∧ ∃ d : ℝ, 1 ≤ d ∧ d ≤ Σw i ∧ ∀v, L.w v = P₀.w v/d := by
  induction invoice with
  | start => exact ⟨le_rfl,1,le_rfl,by simp,fun _=>by simp⟩
  | @step j floor y U L earlier filed factor active paid wages previous =>
    obtain ⟨above,d,one,old,rate⟩ := previous
    have jb : j < b := Nat.lt_of_succ_le above
    refine ⟨jb.le,factor*d,one_le_mul_of_one_le_of_one_le active one,?_,?_⟩
    · rw [←insert_Ico_add_one_left_eq_Ico jb,prod_insert (by simp)]
      exact mul_le_mul paid old (zero_le_one.trans one) (mul_nonneg
        (pow_nonneg (zero_le_one.trans (budget_pos R)) _) (pow_nonneg (zero_le_one.trans (budget_pos R)) _))
    · intro v
      rw [wages v,rate v,div_div,mul_comm d]

end YM.Integration.WilsonReceivedCloseHistory
