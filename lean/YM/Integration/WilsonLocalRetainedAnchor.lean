import YM.Integration.WilsonLocalRetainedReportingWeight

/-! On a fixed physical exterior the incoming fine action can be evaluated
at zero relative angles. Its multiplicative correction then has no held
coarse-field dependence. The original occupied links pay the oscillation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalRetainedAnchor
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestReadout WilsonPhysicalRegisteredForestAction
open WilsonCoherentForestMeasure
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I]

def ratio (R:Run G) {m N per:ℕ} (live:m+1<N) (grade:ℕ)
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free) (z:Sample T B G) : ℝ :=
  let Q:=R.family.path.rep N per (m+1)
  let P:=approximation R (p:=per) live grade
  let U0:=state T B (z.1,0)
  let U:=state T B z
  (Q.eval U0/P.eval U0)*(P.eval U/Q.eval U)

theorem oscillation {q0 p0 qx px a:ℝ} (Q0:0<q0) (P0:0<p0) (Qx:0<qx) (Px:0<px)
    (paid:|(-Real.log qx+Real.log px)-(-Real.log q0+Real.log p0)| ≤ a) :
    let k:=(q0/p0)*(px/qx)
    0 < k ∧ |1-k| ≤ Real.exp a-1 := by
  intro k
  have positive:0 < k:=mul_pos (div_pos Q0 P0) (div_pos Px Qx)
  have logged:Real.log k=(-Real.log qx+Real.log px)-(-Real.log q0+Real.log p0) := by
    rw [show k=q0/p0*(px/qx) from rfl,Real.log_mul (div_ne_zero Q0.ne' P0.ne') (div_ne_zero Px.ne' Qx.ne'),
      Real.log_div Q0.ne' P0.ne',Real.log_div Px.ne' Qx.ne'];ring
  rw [←logged] at paid
  have low:Real.exp (-a) ≤ k:=(Real.exp_le_exp.mpr (abs_le.mp paid).1).trans_eq (Real.exp_log positive)
  have high:k ≤ Real.exp a:=(Real.exp_log positive).symm.trans_le (Real.exp_le_exp.mpr (abs_le.mp paid).2)
  have v:=OriginalMarkedRelativeMoment.deviation (p:=1) (h:=k) (a:=a) zero_le_one
    (by simpa only [mul_one] using low) (by simpa only [mul_one] using high)
  exact ⟨positive,by simpa only [mul_one] using v⟩

theorem purchased (R:Run G) (simple:G.Simple) (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q grade:ℕ) (order:q+5 ≤ grade) {ε:ℝ} (he:0<ε) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio),
    let B:=incident R T d o
    let g:=regulatorRun R.family N per (m+1)
    let k:=ratio R live grade T B
    Measurable k ∧ ∀z,0<k z ∧ |1-k z| ≤ ε*g^q := by
  have revenues:=(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [revenues,WilsonReportingForestPivots.support R simple slow d,
    WilsonHeldRetainedActionRate.fee R simple 2 q grade (by omega) he] with m issued earned cash N live per o T
  intro B g k
  let Q:=R.family.path.rep N per (m+1)
  let P:=approximation R (p:=per) live grade
  let Y:=sites R m per d o
  let E:=moving T B
  have original:=issued N per live
  have qPos:∀U,0 < Q.eval U:=Multi.AxisShift.chosen_positive R.makes.wilson live.le
  have pPos:∀U,0 < P.eval U:=OriginalMarkedRunCovariance.keep_positive R live original
  have qm:= (Q.envelope (R.makes.wilson.represents N per (m+1) live.le).good).meas
  have pm:=(OriginalMarkedRunCovariance.keep_envelope R live original).meas
  have u:=measurable_state (G:=G) T B
  have Zero:Measurable (fun z:Sample T B G=>state T B (z.1,0)):=u.comp (measurable_fst.prodMk measurable_const)
  refine ⟨((qm.comp Zero).div (pm.comp Zero)).mul ((pm.comp u).div (qm.comp u)),?_⟩
  intro z
  have grid:=earned per o
  have frozen:=WilsonForestRetainedFibre.fixed R T E Y (fun e h=>(grid.2 T e h).1) z.1
    (Chart.expLinks G (↥E) z.2*background T B z.1) (Chart.expLinks G (↥E) 0*background T B z.1)
  let U:=state T B z
  let U0:=state T B (z.1,0)
  have buy:=OriginalMarkedLocalPurchase.run R live original Y U U0 frozen
  obtain ⟨pos,err⟩:=oscillation (qPos U0) (pPos U0) (qPos U) (pPos U) buy
  exact ⟨pos,err.trans (cash N per live Y grid.1).2⟩

end YM.Integration.WilsonLocalRetainedAnchor
