import YM.Integration.WilsonIndependentCollarSharpPublication
import YM.Integration.WilsonIndependentCollarMaterialWallet

/-! Publish the named chronological material at its measured teacher time.
The restored per-face invoice is computed from its actual occupied rows. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarDatedPublication
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
variable {n₁:ℕ}{I:Type}[Fintype I]
variable
    (passport:Earn.Passport (R.family.side (i+1) per) (Fin n₁))
    (B:I→Earn.Binder passport (Stock.census (Fin n₁))) (grades:Fin n₁→ℕ)
    (order shelf q:ℕ) (H₀:Fin n₁→ℝ)

/-! The return type is the complete original publication on this exact
named material. Its remaining original school and date premises are preserved. -/
include simple course cut hospital cal chamber in
theorem original (ledger:WilsonOriginalCensusDatedMaterial.Material R N (i+1) q grades (σ₀) B)
    (qfit:q ≤ order)(occupied:1 ≤ op.count)(size:∀v,0 < H₀ v) :
    type_of% (WilsonIndependentCollarSharpPublication.original R simple hk D Q π Γ Ψ course scroll books hi cut op lesson
    cal ahead chamber hospital passport B grades order shelf q H₀ (WilsonIndependentCollarMaterialWallet.bill ledger H₀)
    (WilsonOriginalCensusDatedMaterial.words ledger) qfit occupied size
    (fun z=>(WilsonIndependentCollarMaterialWallet.exact_bill ledger H₀ z size).le)) :=
  WilsonIndependentCollarSharpPublication.original R simple hk D Q π Γ Ψ course scroll books hi cut op lesson
    cal ahead chamber hospital passport B grades order shelf q H₀ (WilsonIndependentCollarMaterialWallet.bill ledger H₀)
    (WilsonOriginalCensusDatedMaterial.words ledger) qfit occupied size
    (fun z=>(WilsonIndependentCollarMaterialWallet.exact_bill ledger H₀ z size).le)

end YM.Integration.WilsonIndependentCollarDatedPublication
end
