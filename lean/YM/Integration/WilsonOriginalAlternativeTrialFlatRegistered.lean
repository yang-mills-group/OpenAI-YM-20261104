import YM.Integration.WilsonOriginalAlternativeTrialFlatOptical
import YM.Integration.WilsonOriginalAlternativeTrialWithdrawal
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialFlatRegistered
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

include simple in
theorem original (n d a p:ℕ) (np:0<n) (load:∀s:marks.Mode,s.val.card ≤ n)
    (C e:ℝ)(cp:0 ≤ C)(ep:0<e):
    ∃start:ℕ,∀ᶠ f:ℕ in atTop,∀ (N per m k b reserve:ℕ) (_top:f+1 ≤ N) (bt:b<f+1),start ≤ b →
    ((f+1-b+reserve:ℕ):ℝ) ≤ C*(1+Real.log (H (f+1)))^d →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per k Ψ → TicketP R.alloy R.kit D Q →
    ∀(X I:Type) [Countable I] [Nonempty X] (o:V → Site (R.family.side (f+1) per))
    (A:Gallery X I o (Ψ (f+1)) marks) (w:V → ℝ), (∀v,0<w v) →
    A.E.Paid w (Ψ (f+1)).p.B (Ψ (f+1)).p.supportExponent 1 →
    A.K.Paid w (Ψ (f+1)).p.B (Ψ (f+1)).p.supportExponent (κ (f+1)) →
    ∀(x:X)(s:marks.Mode)(u i:ℕ),(mu:m ≤ u) → (ui:u ≤ i) → (ib:i ≤ b) → WilsonSingleHardRadius.first R simple ≤ u →
    ∀(Z:Support (R.family.side b per))(center:Site (R.family.side b per)),center∈Z →
    (∀a∈s.val,sites R o bt.le a∈Z) →
    let fee:=Poly.toll (wallet R w bt.le) s
    let roof:=(shards marks s).card+4*(fee+WilsonOriginalFlatOccupiedRate.bill (Ψ b).p Z 1 s.val.card)*
      R.alloy.B.a.clock.hatBeta b*(κ b)
    let gain:=(H (f+1))^a*(Real.exp (n*(reserve:ℝ)*(scale (H (f+1)))^3)*Poly.toll w s)
    let value:=‖actualTransport R.family (N:=N) (fun U=>
      ((A.density x U).part s-((Ψ (f+1)).eval U:ℂ)*(Poly.pass (A.E.log x U)).part s)/((Ψ (f+1)).eval U:ℂ)) (ib.trans bt.le) 1‖
    let budget:=(e*(regulatorRun R.family N per (f+1))^p)*roof
    gain*value ≤ budget ∧ (1 ≤ gain → value ≤ budget):=by
  obtain ⟨start,service⟩:=WilsonOriginalAlternativeTrialFlatOptical.original R simple marks n d a p np load C e cp ep
  refine ⟨start,?_⟩
  filter_upwards [service] with f rates N per m k b reserve top bt late time way D Q π Γ Ψ course ticket
    X I ci ne o A w wp reg hard x s u i mu ui ib fixed Z center near sites
  have due:=rates N per m k b reserve top bt late time way D Q π Γ Ψ course ticket X I o A w wp reg hard x s u i mu ui ib fixed Z center near sites
  have same:=WilsonOriginalAlternativeTrialWithdrawal.original R π Γ Ψ course (mu.trans ui) (ib.trans bt.le) top o A w wp reg hard x s 1
  simpa only [same] using due

end YM.Integration.WilsonOriginalAlternativeTrialFlatRegistered
