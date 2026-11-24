import YM.Integration.WilsonRegisteredCenteredReading
import YM.Integration.WilsonRegisteredJoinedScreen
import YM.Integration.WilsonRegisteredFrozenProduct

/-! Two separately deposited, fully interacting marks and their two true
conditional means on one positive earlier Wilson fibre. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredCenteredPair
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open RG16 ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Pert.Asymptotics
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonCoherentMeasuredChart WilsonRegisteredAngularGate WilsonRegisteredCenteredReading
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "Cl" => R.family.path
local notation "d" => (fun _:Fin 2=>(4:ℕ))

theorem measured (simple:G.Simple) (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (Cl).levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ}
    (pr:0<r) (sr:r<Chart.small G P) (jr:r≤J.r) (p grade:ℕ) (order:p+5≤grade) {ε:ℝ} (he:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ N (interior:m+1<N) per (_ref:R.family.ref 4 ≤ m+1)
    (o:Fin 2→Site (R.family.side (m+1) per)) (v:Fin 2→R.family.label 4) (b H q:Fin 2→ℕ)
    (η:Fin 2→ℂ→L[ℝ]ℝ) (T:Forest ((Cl).levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
    (G':Config G (R.family.side (m+1) per)→ℝ), Envelope G'→GaugeInvariant G'→
    let k:=m+1
    let Q:=(Cl).rep N per k
    let B:=incident R T d o
    let D:=⋂i,screen R m per o (o i) (H i)
    let C:=cold R m per d o ∩ D
    let s:=panel R m per d o T r ∩ state T B ⁻¹' D
    let f:=fun i=>centered R interior.le (v i) (o i) (η i) V
    let a:=fun i=>filed R interior.le (v i) (o i) (b i) (q i) T B (η i) V
    let K:=fun i=>fare R interior.le (v i) (o i) (q i) (η i)
    let P₀:=fun U=>G' U*(f 0 U*f 1 U)
    let cost:=fun U=>|G' U| *(K 0*|f 1 U| +K 1*|f 0 U| +K 0*K 1)
    let integrated:=∫z in s,WilsonCoherentRetainedDriver.value R interior grade T B V z*G' (state T B z)*(a 0 z*a 1 z) ∂law P r T B
    (∀i,b i*(4*Q.p.B+2)+2*Q.p.B≤H i)→(∀i,q i+1≤Q.p.order)→
    |actualAverage R.family (N:=N) (C.indicator P₀) V-integrated| ≤
      (ε*regulatorRun R.family N per k^p)*actualAverage R.family (N:=N) (C.indicator (fun U=>|P₀ U|)) V+
        2*actualAverage R.family (N:=N) (C.indicator cost) V := by
  filter_upwards [WilsonRegisteredJoinedScreen.physical R simple slow J clear P hp pr sr d,
    WilsonRegisteredAngularGate.radius R simple slow J clear d jr, WilsonRegisteredCenteredReading.paid R simple,
    WilsonCoherentRetainedDriver.purchased R simple marks fees slow d p grade order he] with m chart angles probe driver
  intro N interior per ref o v b H q η T V G' eG gG k Q B D C s f a K P₀ cost integrated range active
  let μ:=law P r T B
  let U:=state (G:=G) T B
  let w:=actualConditionalDensity R.family N per m V
  let t:=WilsonCoherentRetainedDriver.value R interior grade T B V
  letI:IsFiniteMeasure μ:=funded P r T B hp pr sr
  have md:MeasurableSet D:=MeasurableSet.iInter (fun i=>visible R m per o (o i) (H i))
  have gd:∀g U,Lattice.gauge g U∈D↔U∈D:=fun g U=>by
    simp only [D,Set.mem_iInter,invariant R m per o _ _ g U]
  have mu:Measurable U:=measurable_state T B
  have ms:MeasurableSet s:=(measurable_panel R m per d o T r).inter (mu md)
  have ew:Envelope w:=WilsonCoherentMeasuredChart.driver R m per N interior.le V
  have obs (i:Fin 2):Envelope (f i) ∧ GaugeInvariant (f i):=observable R interior.le ref (v i) (o i) (η i) V
  have ma (i:Fin 2):Measurable (a i):=WilsonRegisteredCenteredReading.measurable R interior.le ref (v i) (o i) (b i) (q i) T B (η i) V
  have env (Z:Config G (R.family.side k per)→ℝ) (e:Envelope Z):Envelope (fun u=>|Z u|):=
    ⟨e.meas.abs,e.cost.imp fun _ cap u=>by simpa only [Real.norm_eq_abs,abs_abs] using cap u⟩
  have pulled (Z:Config G (R.family.side k per)→ℝ) (e:Envelope Z):Envelope (Z∘U):=
    ⟨e.meas.comp mu,e.cost.imp fun _ cap z=>cap (U z)⟩
  have ef:Envelope P₀:=eG.mul ((obs 0).1.mul (obs 1).1)
  have gi:GaugeInvariant P₀:=fun g u=>congrArg₂ (·*·) (gG g u) (congrArg₂ (·*·) ((obs 0).2 g u) ((obs 1).2 g u))
  have eC:Envelope cost:=(env _ eG).mul ((((Envelope.const (K 0)).mul (env _ (obs 1).1)).add
    ((Envelope.const (K 1)).mul (env _ (obs 0).1))).add (Envelope.const (K 0*K 1)))
  have gC:GaugeInvariant cost:=by
    intro g u
    simp only [cost,gG g u,(obs 0).2 g u,(obs 1).2 g u]
  have first:=chart N interior.le per o D md gd T V P₀ ef gi
  have second:=chart N interior.le per o D md gd T V (fun u=>|P₀ u|) (env _ ef) (fun g u=>congrArg abs (gi g u))
  have third:=chart N interior.le per o D md gd T V cost eC gC
  obtain ⟨mt,change⟩:=driver N interior per o T V
  have bound:∀ᵐ z ∂μ.restrict s,0≤w (U z) ∧ 0≤t z ∧ t z≤2*w (U z) ∧
      |w (U z)-t z| ≤(ε*regulatorRun R.family N per k^p)*w (U z) ∧
      |f 0 (U z)-a 0 z| ≤K 0 ∧ |f 1 (U z)-a 1 z| ≤K 1:=by
    filter_upwards [ae_restrict_mem ms] with z hz
    have hit (i:Fin 2):z∈strip R m per d o (o i) (H i) T r:=⟨hz.1,Set.mem_iInter.mp hz.2 i⟩
    have bill (i:Fin 2):|f i (U z)-a i z|≤K i:=probe N per interior.le ref (v i) (o i) (b i) (H i) (q i) T B (η i) V z
      (range i) (angles N interior.le per o (o i) (H i) T z (hit i)) (active i) (hit i).2.2
    exact ⟨actualConditionalDensity_nonneg R.family R.makes interior.le V _,(change z).2.1,
      (change z).2.2.1,(change z).2.2.2,bill 0,bill 1⟩
  have original:=((pulled _ (ew.mul ef)).integrable (μ.restrict s))
  have costs:=((pulled _ (ew.mul eC)).integrable (μ.restrict s))
  have sold:=WilsonRegisteredFrozenProduct.comparison (μ:=μ.restrict s) (w:=w∘U) (t:=t) (H:=G'∘U)
    (a:=f 0∘U) (b:=f 1∘U) (A:=a 0) (B:=a 1) (k:=K 0) (l:=K 1)
    (by simpa only [P₀,Function.comp_def,mul_assoc] using original)
    (by simpa only [cost,Function.comp_def,mul_assoc] using costs)
    ((mt.mul (eG.meas.comp mu)).mul ((ma 0).mul (ma 1))).aestronglyMeasurable bound
  dsimp only at first second third
  change actualAverage R.family (N:=N) (C.indicator P₀) V=_ at first
  change actualAverage R.family (N:=N) (C.indicator (fun u=>|P₀ u|)) V=_ at second
  change actualAverage R.family (N:=N) (C.indicator cost) V=_ at third
  rw [first,second,third]
  simpa only [integrated,P₀,cost,w,t,U,s,μ,Function.comp_apply,mul_assoc] using sold

end YM.Integration.WilsonRegisteredCenteredPair
end
