import YM.Integration.WilsonLocalHeldRough
import YM.Further.LOCAL_LOG_JETS.Windows

/-! The complete ordered physical lower derivatives use the same exterior
calibration. Every dropped compact configuration is accounted for by its
actual conditional absolute moment. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalHeldDerivatives
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonLocalReportingChartIntegral WilsonLocalHeldKernelChart
open WilsonLocalAnchoredKernel
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I]

def measured (R:Run G) (N per m:ℕ) (V:Config G (R.family.side m per))
    (l:List (Directions G (R.family.side m per))) (U:Config G (R.family.side (m+1) per)) :=
  leftDerivs (fun W=>actualConditionalDensity R.family N per m W U) l V

theorem factor (R:Run G) (N per m:ℕ) (V:Config G (R.family.side m per))
    (l:List (Directions G (R.family.side m per))) (U:Config G (R.family.side (m+1) per)) :
    measured R N per m V l U = leftDerivs (fun W=>reduced R N per m W U) l V*(R.family.path.rep N per (m+1)).eval U := by
  have eq:(fun W=>actualConditionalDensity R.family N per m W U)=fun W=>(R.family.path.rep N per (m+1)).eval U*reduced R N per m W U :=
    funext fun W=>(density R N per m W U).trans (mul_comm ..)
  rw [measured,eq,Further.LogJets.left_constant_mul,mul_comm]

theorem original (R:Run G) (simple:G.Simple) (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (P:ChartRatio G) (hp:LocalRatio P) (J:Voice G) (clear:Clear G J) (d:I→ℕ) (q grade:ℕ) (order:q+5≤grade)
    {ε r:ℝ} (ep:0 < ε) (pr:0 < r) (sr:r < Chart.small G P) (rv:r≤J.r) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
    (l:List (Directions G (R.family.side m per))) (H:Config G (R.family.side (m+1) per)→ℝ) (L:ℝ),
    let D:=measured R N per m V l
    let ρ:=actualConditionalDensity R.family N per m V
    0≤L→Measurable D→Envelope H→GaugeInvariant H→(∀U,|D U|≤L*ρ U)→
    let B:=incident R T d o
    let C:=cold R m per d o
    let a:=forecast P q R live grade T B C (fun F=>leftDerivs F l V) H
    let g:=regulatorRun R.family N per (m+1)
    let ν:=prior G (R.family.side (m+1) per)
    let μ:=law G T B r
    Integrable a μ ∧ |(∫U,D U*H U ∂ν)-(∫z,a z ∂μ)| ≤
      ε*g^q*L*actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V+
        L*actualAverage R.family (N:=N) (Cᶜ.indicator (fun U=>|H U|)) V := by
  filter_upwards [WilsonLocalAnchoredKernel.original R simple marks fees slow P hp J clear d q grade order ep pr sr rv] with m booked N live per o T V l H L
  intro D ρ pos mD eH gi price B C a g ν μ
  let Q:=R.family.path.rep N per (m+1)
  let read:=fun (F:Config G (R.family.side m per)→ℝ)=>leftDerivs F l V
  have qp:∀U,0 < Q.eval U:=Multi.AxisShift.chosen_positive R.makes.wilson live.le
  have incoming:Measurable Q.eval:=(Q.envelope (R.makes.wilson.represents N per (m+1) live.le).good).meas
  have join (U):D U=read (fun W=>reduced R N per m W U)*Q.eval U:=factor R N per m V l U
  have meas:Measurable (fun U=>read (fun W=>reduced R N per m W U)):=by
    convert mD.div incoming using 1
    funext U;exact (eq_div_iff (qp U).ne').mpr (join U).symm
  have reducedCost (U):|read (fun W=>reduced R N per m W U)|≤L*reduced R N per m V U := by
    apply (le_of_mul_le_mul_right · (qp U))
    have h:=price U
    rw [join,abs_mul,abs_of_pos (qp U)] at h
    change _ ≤ L*actualConditionalDensity R.family N per m V U at h
    rw [density,←mul_assoc] at h
    exact h
  obtain ⟨ia,cost⟩:=booked N live per o T V read H L pos meas eH gi reducedCost
  have full:signal R N per m read H=(fun U=>D U*H U):=funext (fun U=>congrArg (·*H U) (join U).symm)
  rw [full] at cost
  have ms:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  have tail:=WilsonLocalHeldRough.original R live.le V D H ms mD eH price
  refine ⟨ia,?_⟩
  calc
    _ ≤ |(∫U,D U*H U ∂ν)-(∫U,C.indicator (fun X=>D X*H X) U ∂ν)|+
        |(∫U,C.indicator (fun X=>D X*H X) U ∂ν)-(∫z,a z ∂μ)|:=abs_sub_le .. 
    _ ≤ _ := (add_le_add tail cost).trans_eq (add_comm ..)

end YM.Integration.WilsonLocalHeldDerivatives
