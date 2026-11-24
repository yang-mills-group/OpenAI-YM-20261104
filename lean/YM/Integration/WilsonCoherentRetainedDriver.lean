import YM.Integration.WilsonIncidentRetainedChart
import YM.Integration.WilsonCoherentMeasuredChart

/-! The retained driver on the same angular sample, with the original
exterior marginal. Its common denominator stays explicitly in the field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentRetainedDriver
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open RG16 ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Pert.Asymptotics
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] {j N per:ℕ}
local notation "A" => R.family.path
local notation "S" => (A).levels.clock.op j per
local notation "Q" => (A).rep N per (j+1)

def value (interior:j+1<N) (grade:ℕ) (T:Forest (S).ratio) (B:Finset T.Free)
    (V:Config G (R.family.side j per)) (z:Sample T B G) : ℝ :=
  WilsonForestRetainedFibre.corrected R (N:=N) T (moving T B) V
    (approximation R (p:=per) interior grade) z.1 (state T B z)

theorem purchased (simple:G.Simple) (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A).levels m))
    (d:I→ℕ) (q grade:ℕ) (order:q+5≤grade) {ε:ℝ} (he:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀N (interior:m+1<N) per (o:I→Site (R.family.side (m+1) per))
    (T:Forest ((A).levels.clock.op m per).ratio) (V:Config G (R.family.side m per)),
    let B:=incident R T d o
    let field:=value R interior grade T B V
    let w:=actualConditionalDensity R.family N per m V
    let g:=regulatorRun R.family N per (m+1)
    Measurable field ∧ ∀z:Sample T B G,
      0<WilsonForestRetainedFibre.mass R (N:=N) T (moving T B) V (approximation R (p:=per) interior grade) z.1 ∧
      0≤field z ∧ field z ≤ 2*w (state T B z) ∧ |w (state T B z)-field z| ≤ ε*g^q*w (state T B z) := by
  have stocks:=(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [stocks,WilsonReportingForestPivots.support R simple slow d,
    WilsonHeldRetainedActionRate.fee R simple 2 q grade (by omega) he,
    WilsonHeldRetainedActionRate.fee R simple 2 0 grade (by omega) zero_lt_one]
    with m offer funded cash twice N interior per o T V
  intro B field w g
  let K:=approximation R (p:=per) interior grade
  let E:=moving T B
  let P0:=(A).rep N per (m+1)
  let W:=WilsonHeldExteriorLaw.weight R N per m V
  let U:=state (G:=G) T B
  let Z:=WilsonForestRetainedFibre.mass R (N:=N) T E V
  have bought:=offer N per interior
  obtain ⟨c,hc,min⟩:=OriginalMarkedGibbsAction.retained_floor R interior bought
  have ep:Envelope (W K):=(WilsonHeldExteriorLaw.regularity R N per m interior.le V K
    (OriginalMarkedRunCovariance.keep_envelope R interior bought) hc min).1
  have eq:Envelope (W P0):=WilsonCoherentMeasuredChart.driver R m per N interior.le V
  have zp:Measurable (Z K):=(WilsonForestMarginal.bounded T E ep).meas
  have zq:Measurable (Z P0):=(WilsonForestMarginal.bounded T E eq).meas
  refine ⟨((ep.meas.comp (measurable_state T B)).mul (zq.comp measurable_fst)).div (zp.comp measurable_fst),?_⟩
  intro z
  let Y:=sites R m per d o
  let a:=OriginalMarkedLocalPurchase.fee R.alloy.B.a (m+1) Y
    ((Real.sqrt 2*regulatorRun R.family N per (m+1+1))^(grade+1))
  have ground:=funded per o
  have cap:Real.exp a-1≤ε*g^q:=(cash N per interior Y ground.1).2
  have small:Real.exp a≤2:=by
    have atOne:= (twice N per interior Y ground.1).2
    change Real.exp a-1≤1*g^0 at atOne
    rw [pow_zero,mul_one] at atOne
    linarith only [atOne]
  have cert:=WilsonForestRetainedFibre.original R T E interior bought Y
    (fun e h=>(ground.2 T e h).1) V z.1
    (Chart.expLinks G (↥E) z.2*background T B z.1)
  have w0:0≤w (U z):=actualConditionalDensity_nonneg R.family R.makes interior.le V (U z)
  have lo:Real.exp (-a)*w (U z)≤field z:=cert.2.1
  have hi:field z≤Real.exp a*w (U z):=cert.2.2
  have dif:=OriginalMarkedRelativeMoment.deviation w0 lo hi
  exact ⟨cert.1,(mul_nonneg (Real.exp_pos _).le w0).trans lo,hi.trans (mul_le_mul_of_nonneg_right small w0),
    dif.trans (mul_le_mul_of_nonneg_right cap w0)⟩

end YM.Integration.WilsonCoherentRetainedDriver
