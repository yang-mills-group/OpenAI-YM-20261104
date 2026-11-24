import YM.Integration.WilsonReportingForestPivotConditional
import YM.Integration.WilsonReportingForestSites
import YM.Integration.WilsonForestRetainedIntegral
import YM.Integration.WilsonHeldRetainedActionRate

/-! The true retained Wilson action on all internal and crossing fine links
incident on the occupied coarse parents. All insertions see the same actual
crossing pivot and the same exterior marginal. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIncidentRetainedChart
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open RG16 ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Pert.Asymptotics
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]

theorem purchased (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r)
    (sr:r<Chart.small G P) (d:I→ℕ) (q grade:ℕ) (order:q+5≤grade) {ε:ℝ} (he:0<ε) :
    ∀ᶠ j:ℕ in atTop,∀N (interior:j+1<N) per (o:I→Site (R.family.side (j+1) per))
      (T:Forest (R.family.path.levels.clock.op j per).ratio) (V:Config G (R.family.side j per))
      (H:Config G (R.family.side (j+1) per)→ℝ),Envelope H→GaugeInvariant H→
      let Pk:=approximation R (p:=per) interior grade
      let B:=incident R T d o
      let E:=moving T B
      let C:=cold R j per d o
      let ν:=Measure.pi (fun _ : ({e:T.Free|e∉E}:Set T.Free)=>G.probHaar)
      let w:=WilsonHeldExteriorLaw.weight R N per j V Pk
      let Z:=WilsonForestRetainedFibre.mass R (N:=N) T E V
      let retained:=∫ v, Z (R.family.path.rep N per (j+1)) v / Z Pk v *
        (∫ y in ball 0 r,Chart.jacobian P y * C.indicator (fun U=>w U*H U)
          (restored T B v (Chart.expLinks G (↥E) y)) ∂Chart.tangent G (↥E)) ∂ν
      |actualAverage R.family (N:=N) (C.indicator H) V - retained| ≤
        ε*regulatorRun R.family N per (j+1)^q * actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V := by
  have stock:=(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  have paid:=WilsonHeldRetainedActionRate.fee R simple 2 q grade (by omega) he
  filter_upwards [stock,WilsonReportingForestPivots.support R simple slow d,paid,
    WilsonReportingForestPivots.original R simple slow J clear P hp pr sr d,relative R simple slow J clear P hp pr sr d]
    with j obtainA land price entire converted N interior per o T V H eh inv Pk B E C ν w Z retained
  let chart (v:({e:T.Free|e∉E}:Set T.Free)→G.El) (h:Config G (R.family.side (j+1) per)→ℝ) :=
    ∫y in ball 0 r,Chart.jacobian P y*C.indicator h (restored T B v (Chart.expLinks G (↥E) y)) ∂Chart.tangent G (↥E)
  have ground:=land per o
  apply WilsonForestRetainedIntegral.tested R T E interior (obtainA N per interior) (sites R j per d o)
    (fun e h=>(ground.2 T e h).1) V C (MeasurableSet.iInter fun i=>House.bath _) chart
    (fun v h mh=>converted per o T v h mh) (fun h e g=>entire N (by omega) per o T V h e g)
    (price N per interior _ ground.1).2 H eh inv

end YM.Integration.WilsonIncidentRetainedChart
