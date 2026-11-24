import YM.Integration.WilsonOriginalTwoFlatIRFlatPosted
import YM.Integration.WilsonOriginalTwoFlatIRFlatPartitions

/-! The absolute cost of dropping higher total grades from a complete
submitted finite-roster ordinary face on the moving flat. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatPaidParts
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (hi:m ≤ i) (cut:i < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Filter MintClock Multi
local notation "H" => Ψ (i+1)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))

open WilsonOlderFreshGraphSlate
variable {n:ℕ}{I:Type}[Fintype I]
  (passport:Earn.Passport (R.family.side (i+1) per) (Fin n))
  (B:I→Earn.Binder passport (Stock.census (Fin n)))(grades:Fin n→ℕ)
  (order shelf q:ℕ)(H₀:Fin n→ℝ)
  (M:WilsonOriginalCensusDatedMaterial.Material R N (i+1) q grades (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) B)
local notation "T" => WilsonOriginalCensusDatedMaterial.words M
local notation "budget" => WilsonIndependentCollarMaterialWallet.bill M H₀
local notation "point" z:max => WilsonOlderFreshGraphPointWallet.point (B z).center
local notation "A" => WilsonOriginalMixedBlockRows.room (Fin n)
local notation "K₀" => (fun _:Fin n=>(⊥:Submodule ℝ ℂ))
local notation "gf" => Coat.gStep (H).beta
local notation "χ" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "D₀" => (∑v:Fin n,grades v)+1
local notation "ink" z:max y:max U:max => ∑'h:(T z).Roster,
  WilsonGeneralArityCopyAccount.term (T z) (B z).center y U h
local notation "value" z:max y:max x:max U:max => (∏v∈(B z).mode.val,(x v).val)*(ink z y U)
local notation "law" => fun (x:Wallet (A))(U:Config G (R.family.side (i+1) per))=>
  ((H).eval U:ℂ) • ∏z:I,(1+Poly.send (B z).mode (value z (gf) x U))
local notation "Ftype" => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  (A) (K₀) grades order shelf op.count i hi (law)
local notation "gain" => WilsonOriginalMixedBlockBudget.roots B budget
local notation "tickets" => fun v=>H₀ v*max 1 (gain)
local notation "base" => fun v=>(H₀ v)⁻¹
local notation "marks" => Stock.census (Fin n)
local notation "pupil" F:max => Oak.student (n:=per) R hk D Q π Γ books hi (F).op (F).lesson
  ahead (A) (F).model order (F).voter

local notation "offered" => WilsonOriginalMixedBlockRows.mounted B (fun z:I=>(T z).rows (point z) disk)
local notation "public" x:max => WilsonOriginalPhysicalFieldsAtBoard.printed (marks) (H)
  (rendered (offered) (H).p (gf)) x


open WilsonOriginalTwoFlatIRFlatLedger
open WilsonReceivedChronologicalMaterialEndpoint (word submitted)
open Pert.Asymptotics


open WilsonOriginalTwoFlatIRFlatPosted (valueAt)
open WilsonOriginalTwoFlatIRFlatPartitions (settled crop)

def tariff (x:Wallet (A))(z:I)(e:Fin (q+1)):ℂ:=
  (∏v∈(B z).mode.val,(x v).val)*Complex.ofReal (occupied M z e)
def wage (x:Wallet (A))(z:I):ℝ:=
  ‖∏v∈(B z).mode.val,(x v).val‖*(2^(q+WilsonCoeffUV.Wheel.Mark.mass grades (B z).mode.val+2)*
    ∑e:Fin (q+1),(T z).fare e)
local notation "money" x:max => tariff (R:=R) (D:=D) (passport:=passport) (B:=B) (grades:=grades) (q:=q) M x
local notation "gross" x:max => wage (R:=R) (D:=D) (passport:=passport) (B:=B) (grades:=grades) (q:=q) M x
local notation "modeOf" => fun z:I=>(B z).mode

theorem evaluated (x:Wallet (A))(g:ℝ):
    valueAt (R:=R) (D:=D) (passport:=passport) (B:=B) (grades:=grades) (q:=q) M x g=
      settled (modeOf) (money x) g:=by
  unfold valueAt WilsonOriginalTwoFlatIRFlatPartitions.settled
  apply prod_congr rfl
  intro j _
  apply congrArg (1+·)
  apply congrArg (Poly.send (B j).mode)
  rw [Complex.ofReal_sum,Finset.mul_sum]
  apply sum_congr rfl
  intro e _
  simp [tariff,Complex.ofReal_mul,Complex.ofReal_pow,mul_left_comm]

theorem original (x:Wallet (A))(g:ℝ)(hg:0≤g)(small:g≤1)(p:ℕ)(s:(marks).Mode):
    ‖(valueAt (R:=R) (D:=D) (passport:=passport) (B:=B) (grades:=grades) (q:=q) M x g).part s-
      (crop (modeOf) (money x) g p).part s‖≤g^(p+1)*∏j,(1+(gross x) j):=by
  rw [evaluated R D passport B grades q M x]
  apply (WilsonOriginalTwoFlatIRFlatPartitions.original (modeOf) (money x) g hg small p s).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hg _)
  apply Finset.prod_le_prod (fun j _=>by positivity)
  intro j _
  apply add_le_add_right
  unfold wage
  rw [Finset.mul_sum,Finset.mul_sum]
  apply sum_le_sum
  intro e _
  rw [tariff,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (WilsonOriginalTwoFlatIRFlatWage.expense M j e) (norm_nonneg _)

end YM.Integration.WilsonOriginalTwoFlatIRFlatPaidParts
end
