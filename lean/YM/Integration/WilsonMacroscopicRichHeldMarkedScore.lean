import YM.Integration.WilsonMacroscopicRichHeldProbePrice
import YM.Integration.WilsonLocalHeldMarginalExperiment

/-! An actual localized nonlinear Wilson variation, averaged on the original lower and upper measures. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichHeldMarkedScore
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonLocalReportingChartIntegral WilsonLocalHeldKernelChart
open WilsonLocalAnchoredKernel WilsonLocalHeldCurvatureMarginal WilsonLocalHeldDerivatives
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I]

open RGComparison.Core16 Push.Local.Kernel WilsonMacroscopicRichTransitionIncome

/-- Relative score with the original fine Wilson density restored, before all periods and cutoffs. -/
theorem score (R : Run G) (m order width : ℕ) {radius : ℝ} (rad : 0 ≤ radius) :
    let L := WilsonMacroscopicRichHeldProbePrice.price R m order width radius
    0 ≤ L ∧ ∀ N per : ℕ, m+1 ≤ N → ∀ (A : Edges (R.family.side m per)), A.card ≤ width →
      ∀ l : List (Directions G (R.family.side m per)), l.length ≤ order → (∀a∈l,Born A radius a) →
      ∀ V : Config G (R.family.side m per), Measurable (measured R N per m V l) ∧
        ∀ U, |measured R N per m V l U| ≤ L*actualConditionalDensity R.family N per m V U := by
  obtain ⟨positive,paid⟩ := WilsonMacroscopicRichHeldProbePrice.original R m order width rad
  refine ⟨positive,?_⟩
  intro N per live A owned l length directions V
  let Q := R.family.path.rep N per (m+1)
  have regular : Envelope Q.eval := RG02.Actual.eval_envelope R.makes.wilson (p:=per) live
  obtain ⟨borel,bound⟩ := paid N per (someSlices _ _) live A owned l length directions V
  constructor
  · change Measurable (fun U => measured R N per m V l U)
    simp_rw [WilsonLocalHeldDerivatives.factor]
    exact borel.mul regular.1
  intro U
  have hot : 0 < (R.family.path.rep N per (m+1)).eval U := RG02.Actual.eval_pos R.makes.wilson (p:=per) live U
  rw [WilsonLocalHeldDerivatives.factor,abs_mul,abs_of_pos hot,WilsonLocalHeldKernelChart.density,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (bound U) hot.le

theorem original (R:Run G) (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (q grade:ℕ) (order:q+5≤grade) (k width:ℕ) {radius:ℝ} (rad:0≤radius)
    {ε r:ℝ} (ep:0<ε) (pr:0<r) (sr:r<Chart.small G P) (rv:r≤J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (A:Edges (R.family.side m per)), A.card≤width → ∀ (l:List (Directions G (R.family.side m per))),
    l.length≤k → (∀a∈l,Born A radius a) → ∀ H:Config G (R.family.side (m+1) per)→ℝ, Envelope H → GaugeInvariant H →
    let L:=WilsonMacroscopicRichHeldProbePrice.price R m k width radius
    let B:=incident R T d o
    let C:=cold R m per d o
    let g:=regulatorRun R.family N per (m+1)
    let ν:=prior G (R.family.side (m+1) per)
    let μ:=law G T B r
    let upper:=scene R.family.path N per (m+1)
    let lower:=scene R.family.path N per m
    let expense:=fun V=>(ε/2)*g^q*L*actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V+
      L*actualAverage R.family (N:=N) (Cᶜ.indicator (fun U=>|H U|)) V
    Integrable expense lower ∧ (∫V,expense V ∂lower) ≤ ε*g^q*L*Real.sqrt (∫U,‖H U‖^2 ∂upper) ∧
    ∀V,let a:=forecast P q R live grade T B C (fun F=>leftDerivs F l V) H
       Integrable a μ ∧ |(∫U,measured R N per m V l U*H U ∂ν)-(∫z,a z ∂μ)| ≤ expense V := by
  filter_upwards [WilsonLocalHeldMarginalExperiment.original R stoves simple marks fees slow P hp J clear d q grade order ep pr sr rv] with m bought N live per o T A widthA l len small H env gi
  obtain ⟨pos,paid⟩ := score R m k width rad
  have measured := paid N per live.le A widthA l len small
  exact bought N live per o T l H _ env gi pos (fun V=>(measured V).1) (fun V=>(measured V).2)

end YM.Integration.WilsonMacroscopicRichHeldMarkedScore
