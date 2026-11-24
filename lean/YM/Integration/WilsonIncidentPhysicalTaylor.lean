import YM.Integration.WilsonCoherentRegisteredCut
import YM.Integration.WilsonIncidentRegisteredMass

/-! The actual full Wilson primary versus its local Taylor polynomial on
the physical registered forest. The original threshold and cutoff occur in
the observables, while the remainder charges only unscaled source sizes. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIncidentPhysicalTaylor
open Function Filter Set Metric Lattice Wilson RG Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato OPE.Therm MSbar.Heath Source Pert.Asymptotics
open WilsonReportingForestPivots WilsonCoherentReportingForest WilsonIncidentRegisteredMass
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]

theorem purchased (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P)
    (d:I→ℕ) (q:ℕ) {ε:ℝ} (he:0<ε) :
    ∀ᶠ j:ℕ in atTop,∀N per, j+1≤N → ∀(y:∀i,R.family.label (d i)) (o:I→Site (R.family.side (j+1) per))
    (T:Forest (R.family.path.levels.clock.op j per).ratio),
    let B:=incident R T d o
    let E:=moving T B
    let θ:=(R.family.path.rep N per (j+1)).p.threshold
    ∀(v:({e:T.Free|e∉E}:Set T.Free)→G.El) (x:↥E→G.Color),
    let U:=restored T B v (Chart.expLinks G (↥E) x)
    x∈ball 0 r → U∈cold R j per d o →
      ‖(∏i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U) -
        WilsonCoherentReportingPivot.row R d θ y o (restored T B v 1) (drift T B x) (q+2*reserve R d) 1‖ ≤
      ε*regulatorRun R.family N per (j+1)^q*originalMass R d y := by
  obtain ⟨C,hC,fields⟩:=WilsonCoherentRegisteredCut.purchased R d simple (q+2*reserve R d)
  filter_upwards [fields,WilsonIncidentRegisteredMass.purchased R simple slow J clear P pr sr d q C hC he]
    with j expand paid N per live y o T B E θ v x U hx accepted
  have bought:=paid N per live y o T v x hx accepted
  exact (expand N (by omega) per o T v x bought.1 accepted y).trans bought.2

end YM.Integration.WilsonIncidentPhysicalTaylor
