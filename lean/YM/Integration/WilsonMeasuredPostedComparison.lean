import YM.Integration.WilsonMeasuredSignedEnvelope
import YM.Integration.WilsonReceivedCoveredEarlier

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMeasuredPostedComparison
open OPE.Therm Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Tree AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV QuadraticLocal.Advent
open Push Push.Local Push.PriceCompiler AnalyticBridge VerifiedReset RemainderComparison
open AllOrder.Transit WheelP PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Pressure ConnectedActivityE6 Filter
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (simple : G.Simple)
variable {m N per k i : ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀ a,Rep G (R.family.side a per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (started : m ≤ i) (live : i ≤ N)
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "W" => (Ψ i)
local notation "P" => R.family.path.rep N per i
local notation "κ" => LocalComparison.forcedDivisor R.family i

include simple course started live

open private joined from YM.Integration.WilsonReceivedCoveredEarlier

theorem earlier (y : Site (R.family.side i per)) (h : Coefficient F (R.family.side i per))
    (fmt : h.Format y R.family.params W) {M : ℝ} (paid : h.remBound y W κ M)
    (actual filed declared : Config G (R.family.side i per) → ℂ)
    (represented : ∀U, h.density y S W U=actual U-((W).eval U:ℂ)*filed U)
    (catalog : RG.Envelope (fun U=>filed U-declared U)) {B : ℝ}
    (fee : (∫U,‖filed U-declared U‖ ∂scene R.family.path N per i)≤B) :
    let error := fun U=>actual U/((W).eval U:ℂ)-declared U-account h W U/((W).eval U:ℂ)
    RG.Envelope error ∧ ∀ (j : ℕ) (age : j ≤ i),
      (∫V,‖actualTransport R.family (N:=N) error age V‖ ∂scene R.family.path N per j)≤B+(‖h.x 0‖+M) := by
  intro error
  have signed := WilsonMeasuredSignedEnvelope.original R simple π Γ Ψ course started live y h fmt paid
    actual filed represented
  have combined := joined R live _ _ catalog signed.1 B _ fee signed.2
  have agree : error=fun U=>(filed U-declared U)+(actual U/((W).eval U:ℂ)-filed U-account h W U/((W).eval U:ℂ)) :=
    funext fun U=>by dsimp only [error]; abel
  exact agree ▸ combined

end YM.Integration.WilsonMeasuredPostedComparison
