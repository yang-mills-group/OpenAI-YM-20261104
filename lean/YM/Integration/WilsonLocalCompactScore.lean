import YM.Integration.WilsonLocalCompactKernel

/-! Each true held-boundary response integrated on the full compact
Wilson forest, with the exact forced activity and its charges retained. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactScore
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Further.LogJets
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestReadout WilsonPhysicalRegisteredForestAction
open WilsonCoherentForestMeasure WilsonLocalRetainedCompactFibre WilsonLocalHeldKernelChart WilsonLocalCompactKernel
open WilsonLocalHeldDerivatives WilsonLocalAnchoredKernel
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I]

theorem original (R:Run G) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade) {ε:ℝ} (ep:0<ε) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
    (l:List (Directions G (R.family.side m per))) (H:Config G (R.family.side (m+1) per)→ℝ) (L:ℝ),
    let D:=measured R N per m V l
    let ρ:=actualConditionalDensity R.family N per m V
    0≤L → Measurable D → Envelope H → GaugeInvariant H → (∀U,|D U|≤L*ρ U) →
    let F:=fun U=>leftDerivs (fun W=>reduced R N per m W U) l V*H U
    let A:=adjusted R live grade T (incident R T d o) F
    let P:=approximation R (p:=per) live grade
    let Q:=R.family.path.rep N per (m+1)
    let g:=regulatorRun R.family N per (m+1)
    let ν:=prior G (R.family.side (m+1) per)
    P.activities.forced=Q.activities.forced ∧ P.activities.K=Q.activities.K ∧ Integrable A (T.order G) ∧
    |(∫U,D U*H U ∂ν)-(∫u,A u ∂T.order G)|≤ε*g^q*∫U,‖D U*H U‖ ∂ν := by
  have revenue:=(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [signed R simple marks fees slow d q grade ord ep,revenue] with m paid offer N live per o T V l H L
  intro D ρ pos mD eH gi price F A P Q g ν
  let read:=fun (Y:Config G (R.family.side m per)→ℝ)=>leftDerivs Y l V
  have qp:∀U,0<Q.eval U:=Multi.AxisShift.chosen_positive R.makes.wilson live.le
  have incoming:Measurable Q.eval:=(Q.envelope (R.makes.wilson.represents N per (m+1) live.le).good).meas
  have join (U):D U=read (fun W=>reduced R N per m W U)*Q.eval U:=factor R N per m V l U
  have meas:Measurable (fun U=>read (fun W=>reduced R N per m W U)):=by
    convert mD.div incoming using 1
    funext U;exact (eq_div_iff (qp U).ne').mpr (join U).symm
  have reducedCost (U):|read (fun W=>reduced R N per m W U)|≤L*reduced R N per m V U := by
    apply (le_of_mul_le_mul_right · (qp U))
    have h:=price U
    rw [join,abs_mul,abs_of_pos (qp U)] at h
    change _≤L*actualConditionalDensity R.family N per m V U at h
    rw [density,←mul_assoc] at h
    exact h
  have receipt:=WilsonLocalAnchoredKernel.source R live.le V read H pos meas eH gi reducedCost
  have signalEq:(fun U=>Q.eval U*F U)=signal R N per m read H:=by
    funext U;change _=read _*Q.eval U*H U;dsimp only [F,read];ring
  have trueEq:signal R N per m read H=(fun U=>D U*H U):=funext fun U=>congrArg (·*H U) (join U).symm
  have purchase:=paid N live per o T F (meas.mul eH.meas) (signalEq.symm ▸ receipt.1) (signalEq.symm ▸ receipt.2.1)
  have eq (U):Q.eval U*F U=D U*H U:=congrFun (signalEq.trans trueEq) U
  have earlier:=offer N per live
  have loss:=purchase.2
  change |(∫U,Q.eval U*F U ∂ν)-(∫u,A u ∂T.order G)|≤ε*g^q*∫U,‖Q.eval U*F U‖ ∂ν at loss
  exact ⟨earlier.forced,earlier.charges,purchase.1,by simpa only [eq] using loss⟩

end YM.Integration.WilsonLocalCompactScore
