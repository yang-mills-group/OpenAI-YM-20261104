import YM.Integration.WilsonOriginalTwoFlatIRFlatLedger
import YM.Integration.WilsonReceivedChronologicalMaterialEndpoint

/-! At the shared moving flat the actual normalized Wilson numerator of the
submitted programme has a finite ordinary face product. Each summand is the
cover scalar of the independently deposited word, at the physical coupling. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatPosted
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

def valueAt (x:Wallet (A))(g:ℝ):Poly (marks):=
  ∏z:I,(1+Poly.send (B z).mode ((∏v∈(B z).mode.val,(x v).val)*
    Complex.ofReal (∑e:Fin (q+1),g^e.val*occupied M z e)))

theorem body (x:Wallet (A)):
    word R D Ψ passport B grades q M x 1=valueAt (R:=R) (D:=D) (passport:=passport) (B:=B) (grades:=grades) (q:=q) M x (gf):=by
  unfold word valueAt
  apply Finset.prod_congr rfl
  intro z _
  rw [WilsonOriginalTwoFlatIRFlatLedger.original M z]

include course cut in
theorem original (tol:ℝ)(paid:WilsonOriginalCensusMaterialPosting.Posted R hk D Q π Γ Ψ books hi op lesson
    ahead passport B grades order shelf q H₀ M tol)(x:Wallet (A)):
    ∃Z:WilsonOriginalDatedCensusInput.Filed (N:=N) R hk D Q π Γ Ψ books hi ahead
      (tickets) (((D₀)+5)*(Fintype.card (Fin n))) (submitted R D Ψ passport B grades q M x),
      Z.x=x ∧ Z.grades=grades ∧ Z.post.passport=passport ∧
      ∀s:(marks).Mode,((R.family.path.rep N per (i+1)).eval 1:ℂ)⁻¹*
          ((submitted R D Ψ passport B grades q M x) 1).part s=
        (valueAt (R:=R) (D:=D) (passport:=passport) (B:=B) (grades:=grades) (q:=q) M x (regulatorRun R.family N per (i+1))).part s:=by
  obtain ⟨Z,zx,gr,ps,all⟩:=WilsonReceivedChronologicalMaterialEndpoint.original R hk D Q π Γ Ψ
    course books hi cut op lesson ahead passport B grades order shelf q H₀ M tol paid x
  refine ⟨Z,zx,gr,ps,fun s=>?_⟩
  calc
    _= (word R D Ψ passport B grades q M x 1).part s:=all 1 s
    _= _:=by
      rw [body,WilsonReceivedChronologicalMaterialEndpoint.heat R π Γ Ψ course hi cut]
      rfl

end YM.Integration.WilsonOriginalTwoFlatIRFlatPosted
end
