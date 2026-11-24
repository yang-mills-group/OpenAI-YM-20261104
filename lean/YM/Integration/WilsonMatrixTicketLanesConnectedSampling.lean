import YM.Integration.WilsonMatrixTicketLanesConnectedSites
import YM.Integration.WilsonMatrixTicketLanesConnectedPositive

/-! The true finite compact covariance on the actual measured period and the signed test's two parent sites. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedSampling
open Function Filter Set Real Lattice Gauge RG Tree Wilson Source Marker Extraction Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Extraction.Order RGComparison.Core16 RGComparison.Core16.Spool
open Pert.Asymptotics
open WilsonInvariantActionSeparatedCells Table Climb Trace.Pilot Next.UVStress
open WilsonMatrixTicketLanesReflectedGauge WilsonMatrixTicketLanesConnectedBudget WilsonMatrixTicketLanesConnectedForecast
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)

/-- The mesh is fixed before both period and cutoff, while the two sites still range over the whole signed test. -/
def Row (e : Request G) (ε : ℝ) (m : ℝ→ℕ) (φ : Test 2) (r : ℝ) : Prop :=
  ∀ b,b+1=m r → ∀ (hr : 0<r) N p (upper : b+1 ≤ N) (x : Fin 2→Site (R.family.side N p)),
    WilsonExternalMeshMass.charge R.family (dilate hr φ) x≠0 →
    let o:=fun i=>(R.family.S.toDepth upper p).parent (x i)
    let S:=R.family.path.levels.clock.op b p
    ∀ (_T : Forest S.ratio), Bid.Larger (G:=G) S → ∀ (u : Directions G (R.family.side b p)),
    (∀i,‖u i‖ ≤ (e.2.2:ℝ)+1) →
    let g:=regulatorRun R.family N p (b+1)
    |measured S u R (row e) (col e) (left e) (right e) (fun _=>o 0) (fun _=>o 1) g| ≤ ε*g^e.2.1

theorem original (simple : G.Simple) (paid : Paid G R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    (e : Request G) (ε : ℝ) (positive : 0<ε) {B : ℕ} (large : 17 ≤ B) (φ : Test 2) :
    ∀ᶠ r in trail,Row R e ε (WilsonMeasuredWindow.stop R.family.path.levels simple B) φ r:=by
  let m:=WilsonMeasuredWindow.stop R.family.path.levels simple B
  obtain ⟨grows,_⟩:=WilsonFundedMeasuredWindow.all_radii R pace simple (B:=B) (by omega)
  obtain ⟨a,accepted⟩:=eventually_atTop.mp (WilsonMatrixTicketLanesConnectedPositive.original R simple paid e ε positive)
  filter_upwards [grows.eventually_ge_atTop (a+1),WilsonMatrixTicketLanesConnectedSites.original R simple pace large φ (first e) (second e)]
    with r stage sites b date hr N p upper x live o S T actual u pin
  change b+1=m r at date
  have willing:a ≤ b:=by change a+1 ≤ m r at stage;rw [←date] at stage;exact Nat.le_of_succ_le_succ stage
  obtain ⟨H,far,apart⟩:=sites b date hr N p upper x live
  exact accepted b willing N p upper T actual u pin (fun _=>o 0) (fun _=>o 1) H far apart

end YM.Integration.WilsonMatrixTicketLanesConnectedSampling
