import YM.Integration.WilsonLocalRetainedAnchor

/-! The numerical old-action comparison on all compact values of a
physical fibre, with the actual exterior held fixed. Neither the
reference field nor its comparison requires an angular-coordinate cut. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalRetainedCompactFibre
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestReadout WilsonPhysicalRegisteredForestAction
open WilsonCoherentForestMeasure WilsonLocalRetainedAnchor
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I]

def base (R:Run G) {m N per:ℕ} (live:m+1<N) (grade:ℕ) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (B:Finset T.Free) (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) :=
  let U0:=state (G:=G) T B (v,0)
  (R.family.path.rep N per (m+1)).eval U0/(approximation R (p:=per) live grade).eval U0

theorem scale {a b d:ℝ} (ha:0<a) (small:|1-b/a|≤d):|a-b|≤d*a := by
  have id:a-b=a*(1-b/a):=by field_simp
  rw [id,abs_mul,abs_of_pos ha,mul_comm d]
  exact mul_le_mul_of_nonneg_left small ha.le

theorem contrast {a b x y d:ℝ} (ha:0<a) (hb:0<b) (hx:0<x) (hy:0<y)
    (first:|1-(a/b)*(y/x)|≤d) (last:|1-(x/y)*(b/a)|≤d) :
    |x-(a/b)*y|≤d*x ∧ |x-(a/b)*y|≤d*((a/b)*y) := by
  have f:|1-(a/b)*y/x|≤d:=by simpa only [div_eq_mul_inv,mul_assoc] using first
  have eq:x/(a/b*y)=(x/y)*(b/a):=by field_simp
  have back:=scale (mul_pos (div_pos ha hb) hy) (b:=x) (d:=d) (eq ▸ last)
  exact ⟨scale hx f,(abs_sub_comm ..).le.trans back⟩

theorem fields (R:Run G) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade) {ε:ℝ} (ep:0<ε) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio),
    let B:=incident R T d o
    let E:=moving T B
    let Q:=R.family.path.rep N per (m+1)
    let P:=approximation R (p:=per) live grade
    let g:=regulatorRun R.family N per (m+1)
    ∀v:({e:T.Free|e∉E}:Set T.Free)→G.El,let α:=base R live grade T B v
      0<α ∧ ∀x:↥E→G.El,let U:=filled T E v x
        |Q.eval U-α*P.eval U|≤ε*g^q*Q.eval U ∧ |Q.eval U-α*P.eval U|≤ε*g^q*(α*P.eval U) := by
  have revenue:=(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [revenue,WilsonReportingForestPivots.support R simple slow d,WilsonHeldRetainedActionRate.fee R simple 2 q grade (by omega) ep]
    with m offer grid price N live per o T
  intro B E Q P g v α
  let Y:=sites R m per d o
  let U0:=state (G:=G) T B (v,0)
  have earned:=offer N per live
  have qp:∀U,0<Q.eval U:=Multi.AxisShift.chosen_positive R.makes.wilson live.le
  have pp:∀U,0<P.eval U:=OriginalMarkedRunCovariance.keep_positive R live earned
  have ap:0<α:=div_pos (qp U0) (pp U0)
  refine ⟨ap,fun x=>?_⟩
  intro U
  have bounded:=grid per o
  have fixed:=WilsonForestRetainedFibre.fixed R T E Y (fun e he=>(bounded.2 T e he).1) v x
    (Chart.expLinks G (↥E) 0*background T B v)
  have sale:=OriginalMarkedLocalPurchase.run R live earned Y U U0 fixed
  have reverse:|(-Real.log (Q.eval U0)+Real.log (P.eval U0))-(-Real.log (Q.eval U)+Real.log (P.eval U))|≤_ :=
    (abs_sub_comm ..).le.trans sale
  have first:=((oscillation (qp U0) (pp U0) (qp U) (pp U) sale).2).trans (price N per live Y bounded.1).2
  have last:=((oscillation (qp U) (pp U) (qp U0) (pp U0) reverse).2).trans (price N per live Y bounded.1).2
  exact contrast (qp U0) (pp U0) (qp U) (pp U) first last

end YM.Integration.WilsonLocalRetainedCompactFibre
