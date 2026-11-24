import YM.Integration.WilsonNeutralTwoPrintPathPostedWallet
import YM.Integration.WilsonOriginalFixedTestCensusPairedTickets
import YM.Integration.WilsonOriginalFixedTestCensusOffer

/-! Rent and inverse wallets of the exact voter used by the sparse hearing on a filed book. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFixedTestCensusPaidVote
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


local notation "χ₀" => R.family.path.levels.clock.hatBeta i


variable {tol:ℝ}(file:WilsonOriginalCensusMaterialPosting.Posted R hk D Q π Γ Ψ books hi
    op lesson ahead passport B grades order shelf q H₀ M tol)
local notation "vote" x:max => WilsonNeutralTwoPrintPathPostedWallet.vote R hk D Q π Γ Ψ books hi
  op lesson ahead passport B grades order shelf q H₀ M file x

/-- One clock above the book's own date may be shared with an adjacent book. -/
theorem original (x:Wallet (A))(positive:∀v,0<H₀ v)(c:ℝ)(later:χ₀≤c)(dose:Fin n→ℕ)
    (charged:∀v,(tickets) v≤c^(dose v)):
    (vote x).x=x ∧ (vote x).law=(law) ∧ HEq (vote x).post file.choose ∧
    (vote x).post.w=file.choose.w ∧ (vote x).post.rent=file.choose.rent ∧
    file.choose.input.hard.Paid file.choose.w (H).p.B (H).p.supportExponent
      (R.family.path.levels.clock.forcedAllowance (i+1)) ∧
    (8*(budgetR R i)^(vote x).post.op.count)*(vote x).post.rent≤tol ∧
    ∀s:(marks).Mode,(Poly.toll (vote x).post.w s)⁻¹≤
      c^(((D₀)+5)*Fintype.card (Fin n)+∑v∈s.val,dose v):=by
  obtain ⟨_,_,_,_,_,_,hard,rent,_,hear⟩:=file.choose_spec
  obtain ⟨wallet,_,_,_,seats,law',same,_,_,_,width,rent'⟩:=
    (file.choose_spec.2.2.2.2.2.2.2.2.2 x).choose_spec
  refine ⟨wallet,law',same,width,rent',hard,WilsonOriginalFixedTestCensusOffer.high_rent
    R hk D Q π Γ Ψ books hi ahead (vote x) seats rent' rent,?_⟩
  intro s
  have nonneg:0≤χ₀:=zero_le_one.trans (R.alloy.B.a.fits.delayed i).le
  have a:=WilsonOriginalFixedTestCensusOffer.inverse R hk D Q π Γ Ψ books hi ahead (vote x) s
  refine a.trans ?_
  rw [pow_add,Poly.toll,←Finset.prod_pow_eq_pow_sum]
  exact mul_le_mul (pow_le_pow_left₀ nonneg later _) (Finset.prod_le_prod
    (fun v _=>mul_nonneg (positive v).le (zero_le_one.trans (le_max_left ..)))
    (fun v _=>charged v)) (Finset.prod_nonneg (fun v _=>mul_nonneg (positive v).le
      (zero_le_one.trans (le_max_left ..)))) (pow_nonneg (nonneg.trans later) _)

end YM.Integration.WilsonOriginalFixedTestCensusPaidVote
end
