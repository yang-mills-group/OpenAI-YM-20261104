import YM.Integration.WilsonOriginalTwoFlatIRCapturedCross
import YM.Integration.WilsonOriginalTwoFlatIRCapturedPrinted
import YM.Integration.WilsonOriginalTwoFlatIRMounted
import YM.Integration.WilsonOriginalTwoFlatIRFlatLedger
import YM.Integration.WilsonReceivedChronologicalMaterialEndpoint

/-! At the shared moving flat the actual normalized Wilson numerator of the
submitted programme has a finite ordinary face product. Each summand is the
cover scalar of the independently deposited word, at the physical coupling. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalTwoFlatIRCapturedPrice
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


open WilsonOriginalCensusDatedMaterial (words)

open Planned.GuardedAtom Extra.Histories Next.Foundations RG16 RG16.Literal Trace.Physical.GermGraph
open WilsonOriginalTwoFlatIRHalo WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open WilsonOriginalTwoFlatIRCapturedCross (Quote)
local notation "rep" => R.family.path.rep N per (i+1)
local notation "coupling" => regulatorRun R.family N per (i+1)

include course cut in
theorem original (tol:ℝ)(posted:WilsonOriginalCensusMaterialPosting.Posted R hk D Q π Γ Ψ books hi op lesson ahead
    passport B grades order shelf q H₀ M tol)(x:Wallet (A)){u v P depth:ℕ}(uc : u  ≤  (i + 1)) (vc : v  ≤  (i + 1))
    (quote:Quote R N per u v (i+1) P depth uc vc){U ξ K:ℝ}{ext:ℕ}
    (dep:q ≤ order)(oc:1 ≤ op.count)(slots:Fintype.card (Fin n) ≤ op.count)(fit:(∑a,grades a) ≤ shelf)
    (fund:Invoice.Supports (rep).p U ((rep).p.supportExponent+2) coupling (σ₀) ξ)
    (fare:Invoice.price (rep).p U (order+shelf+1) op.count ((rep).p.supportExponent+2) ξ G ≤ 
      (2:ℝ)^(order+shelf+1)*(3*(coupling)⁻¹)^2)
    (income:(∑z:I,Real.exp ((σ₀)*(B z).length)*WilsonIndependentCollarSlateIntensity.amount (words M z)
      (B z).center) ≤ K*(3*(coupling)⁻¹)^ext)
    (s:(marks).Mode)(Z:Support (R.family.side (i+1) per))(center:0∈Z)(reside:∀a∈s.val,passport.origin a∈Z)
    (rad:ℕ)(near:∀a∈s.val,separation (passport.origin a) 0 ≤ rad)(inside:rad ≤ (rep).p.B)
    (housed:Z⊆halo (rep).p.B {0}){α:ℝ}(strip:(rep).p.supportExponent ≤ α)
    (ou:Opened R.family 0 u per)(ov:Opened R.family 0 v per)
    (reach:4*(P+(power s.val.card ((∑a,grades a)+1+2+ext)+0+2)) ≤ depth):
    let h:=((2:ℝ)^(order+shelf+1))^2*max 1 K
    let e:=power s.val.card ((∑a,grades a)+1+2+ext)+0+2
    let bill:=WilsonOriginalTwoFlatIRFiled.reserve (roof (marks) s (R.family.localSection 0) R.family.params α h) 1*3^e
    let numerator:=fun V=>(submitted R D Ψ passport B grades q M x V).part s
    ‖reading R (N:=N) numerator u uc-reading R (N:=N) numerator v vc‖ ≤ bill*coupling^P:=by
  obtain ⟨F,_,_,_,filed⟩:=WilsonOriginalTwoFlatIRCapturedPrinted.original R hk D Q π Γ Ψ
    course books hi cut op lesson ahead passport B grades order shelf q H₀ M tol posted x
  exact quote B grades (words M) M.radius.le dep oc slots fit fund fare income s Z center reside rad near inside
    housed strip ou ov reach x _ (fun V=>filed V s)

end YM.Integration.WilsonOriginalTwoFlatIRCapturedPrice
end
