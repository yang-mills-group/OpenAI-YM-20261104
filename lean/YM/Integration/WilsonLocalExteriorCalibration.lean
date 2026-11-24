import YM.Integration.WilsonLocalRetainedCompactFibre
import YM.Integration.WilsonLocalHeldKernelIntegral

/-! Signed tests on the whole finite fibre, including the true held-field
kernel. The fine action is replaced with the separately filed action
and one exterior value that is independent of the held coarse field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalExteriorCalibration
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestReadout WilsonPhysicalRegisteredForestAction
open WilsonCoherentForestMeasure WilsonLocalRetainedCompactFibre
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I]

theorem tested (R:Run G) (simple:G.Simple)
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
    ∀H:Config G (R.family.side (m+1) per)→ℝ,Measurable H →
      let U:=filled (G:=G) T E v
      let μ:=Chart.physical G (↥E)
      let h:=fun x=>Q.eval (U x)*H (U x)
      let b:=fun x=>(α*P.eval (U x))*H (U x)
      Integrable h μ → Integrable b μ ∧ |(∫x,h x ∂μ)-(∫x,b x ∂μ)|≤ε*g^q*∫x,‖h x‖ ∂μ := by
  have revenue:=(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [revenue,fields R simple marks fees slow d q grade ord ep] with m offer estimates N live per o T
  intro B E Q P g v α H mh U μ h b ih
  have mp:=OriginalMarkedRunCovariance.keep_envelope R live (offer N per live)
  have mu:Measurable U:=T.continuous_drape.measurable.comp ((cut T E).symm.measurable.comp (measurable_id.prodMk measurable_const))
  have mb:Measurable b:=(measurable_const.mul (mp.meas.comp mu)).mul (mh.comp mu)
  have qp:∀Y,0<Q.eval Y:=Multi.AxisShift.chosen_positive R.makes.wilson live.le
  apply WilsonLocalReportingDensityIntegral.difference μ ih mb
  filter_upwards [] with x
  exact WilsonLocalHeldKernelIntegral.point _ _ _ _ (qp (U x)).le ((estimates N live per o T v).2 x).1

theorem ratio {a w z δ:ℝ} (ap:0<a) (wp:0<w) (rate:|w-w*(z/a)|≤δ*w):|z-a|≤δ*a := by
  rw [show w-w*(z/a)=w*(1-z/a) by ring,abs_mul,abs_of_pos wp,mul_comm δ w] at rate
  exact (abs_sub_comm z a).le.trans (scale ap (le_of_mul_le_mul_left rate wp))

theorem represented (k p q b y z:ℝ) (pp:p≠0) (qp:q≠0) (bp:b≠0) (zp:z≠0) :
    (k*p/b)*y/z=(k*q/b)*((y/z)/(q/p)) := by
  field_simp

theorem normalizer (R:Run G) (simple:G.Simple)
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
    ∀ (V:Config G (R.family.side m per)) (v:({e:T.Free|e∉E}:Set T.Free)→G.El),
      let α:=base R live grade T B v
      let zQ:=WilsonForestRetainedFibre.mass R (N:=N) T E V Q v
      let zP:=WilsonForestRetainedFibre.mass R (N:=N) T E V P v
      0<zP ∧ 0<α ∧ |zQ/zP-α|≤ε*g^q*α := by
  have revenue:=(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [revenue,WilsonCoherentRetainedDriver.purchased R simple marks fees slow d q grade ord ep] with m offer paid N live per o T
  intro B E Q P g V v α zQ zP
  let U0:=state (G:=G) T B (v,0)
  let ρ:=actualConditionalDensity R.family N per m V U0
  have qp:=Multi.AxisShift.chosen_positive R.makes.wilson live.le U0
  have pp:=OriginalMarkedRunCovariance.keep_positive R live (offer N per live) U0
  have ap:0<α:=div_pos qp pp
  have billed:=(paid N live per o T V).2 (v,0)
  have zp:0<zP:=billed.1
  have lo:=WilsonHeldExteriorLaw.upper_floor R N per m live.le
  obtain ⟨u,hu,floor⟩:=lo
  have Ω:Envelope Q.eval:=Q.envelope (R.makes.wilson.represents N per (m+1) live.le).good
  obtain ⟨_,κ,hκ,bound⟩:=WilsonHeldExteriorLaw.regularity R N per m live.le V Q Ω hu floor
  have rp:0<ρ:=hκ.trans_le (bound U0)
  have eq:WilsonForestRetainedFibre.corrected R (N:=N) T E V P v U0=ρ*((zQ/zP)/α):=by
    change (_*P.eval U0/_)*zQ/zP=(_*Q.eval U0/_)*((zQ/zP)/(Q.eval U0/P.eval U0))
    exact represented _ _ _ _ _ _ pp.ne' qp.ne' (Multi.AxisShift.chosen_positive R.makes.wilson (by omega) V).ne' zp.ne' 
  refine ⟨zp,ap,ratio ap rp ?_⟩
  rw [←eq]
  exact billed.2.2.2

end YM.Integration.WilsonLocalExteriorCalibration
