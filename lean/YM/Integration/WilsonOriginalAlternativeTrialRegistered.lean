import YM.Integration.WilsonOriginalAlternativeTrialWithdrawal
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialRegistered
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable {V:Type} [DecidableEq V] [Fintype V] (marks:Marker.Census V)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

open private YM.Push.Local.gasRate_le from YM.Push.LOCAL_SPLITTING.Delay
include simple in
theorem original (n d a p:ℕ) (np:0<n) (load:∀s:marks.Mode,s.val.card ≤ n)
    (C e:ℝ)(cp:0 ≤ C)(ep:0<e):
    ∃start:ℕ,∀ᶠ f:ℕ in atTop,∀ (N per m k b reserve:ℕ) (_top:f+1 ≤ N) (bt:b ≤ f+1),start ≤ b → m ≤ b →
    ((f+1-b+reserve:ℕ):ℝ) ≤ C*(1+Real.log (H (f+1)))^d →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(X I:Type) [Countable I] [Nonempty X] (o:V → Site (R.family.side (f+1) per))
    (A:Gallery X I o (Ψ (f+1)) marks) (w:V → ℝ), (∀v,0<w v) →
    A.E.Paid w (Ψ (f+1)).p.B (Ψ (f+1)).p.supportExponent 1 →
    A.K.Paid w (Ψ (f+1)).p.B (Ψ (f+1)).p.supportExponent (κ (f+1)) →
    ∀(x:X)(s:marks.Mode)(W:Config G (R.family.side b per)),flags (Ψ b).p.threshold W=∅ →
    let gain:=(H (f+1))^a*(Real.exp (n*(reserve:ℝ)*(scale (H (f+1)))^3)*Poly.toll w s)
    let value:=‖actualTransport R.family (N:=N) (fun U=>
      ((A.density x U).part s-((Ψ (f+1)).eval U:ℂ)*(Poly.pass (A.E.log x U)).part s)/((Ψ (f+1)).eval U:ℂ)) bt W‖
    let budget:=(e*(regulatorRun R.family N per (f+1))^p)*(shards marks s).card
    gain*value ≤ budget ∧ (1 ≤ gain → value ≤ budget):=by
  obtain ⟨start,service⟩:=WilsonOriginalAlternativeTrialOptical.original R simple marks n d a p np load C e cp ep
  refine ⟨start,?_⟩
  filter_upwards [service] with f rates N per m k b reserve top bt sb mb span way D Q π Γ Ψ course ticket
    X I hc hx o A w wp reg hard x s W clear
  have price:=rates N per m k b reserve top bt sb mb span way D Q π Γ Ψ course ticket X I o A w wp reg hard x s W clear
  have paid:=WilsonOriginalAlternativeTrialWithdrawal.original R π Γ Ψ course mb bt top o A w wp reg hard x s W
  simpa only [paid] using price

end YM.Integration.WilsonOriginalAlternativeTrialRegistered
