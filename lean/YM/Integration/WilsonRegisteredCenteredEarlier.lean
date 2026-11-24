import YM.Integration.WilsonRegisteredCenteredPair
import YM.Integration.WilsonRegisteredHeldMoment

/-! The financed signed joint experiment, still on its original Wilson
trajectory, after every further normalized lower integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredCenteredEarlier
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open RG16 ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Pert.Asymptotics
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonCoherentMeasuredChart WilsonRegisteredAngularGate WilsonRegisteredCenteredReading
open private received absolute from YM.Integration.WilsonCoherentLowerExperiment
open private finite_kernel from YM.Integration.WilsonCoherentHeldField
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
    (η:Fin 2→ℂ→L[ℝ]ℝ) (T:Forest ((Cl).levels.clock.op m per).ratio)
    (G':Config G (R.family.side (m+1) per)→ℝ), Envelope G'→GaugeInvariant G'→
    ∀(L:Config G (R.family.side m per)→ℝ), Envelope L→∀u (earlier:u ≤ m) (W:Config G (R.family.side u per)),
    let k:=m+1
    let Q:=(Cl).rep N per k
    let B:=incident R T d o
    let D:=⋂i,screen R m per o (o i) (H i)
    let C:=cold R m per d o ∩ D
    let s:=panel R m per d o T r ∩ state T B ⁻¹' D
    let f:=fun i=>centered R interior.le (v i) (o i) (η i)
    let a:=fun i=>filed R interior.le (v i) (o i) (b i) (q i) T B (η i)
    let K:=fun i=>fare R interior.le (v i) (o i) (q i) (η i)
    let P₀:=fun V U=>G' U*(f 0 V U*f 1 V U)
    let cost:=fun V U=>|G' U| *(K 0*|f 1 V U| +K 1*|f 0 V U| +K 0*K 1)
    let front:=fun V=>actualAverage R.family (N:=N) (C.indicator (P₀ V)) V
    let second:=fun V=>actualAverage R.family (N:=N) (C.indicator (fun U=>|P₀ V U|)) V
    let third:=fun V=>actualAverage R.family (N:=N) (C.indicator (cost V)) V
    let retained:=fun V=>∫z in s,WilsonCoherentRetainedDriver.value R interior grade T B V z*
      G' (state T B z)*(a 0 V z*a 1 V z) ∂law P r T B
    let transfer:=fun h:Config G (R.family.side m per)→ℝ=>actualTransport R.family (N:=N) h earlier W
    (∀i,b i*(4*Q.p.B+2)+2*Q.p.B≤H i)→(∀i,q i+1≤Q.p.order)→
    |transfer (fun V=>L V*front V)-transfer (fun V=>L V*retained V)|≤
      (ε*regulatorRun R.family N per k^p)*transfer (fun V=>|L V| *second V)+
        2*transfer (fun V=>|L V| *third V) := by
  have stocks:=(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [WilsonRegisteredCenteredPair.measured R simple marks fees slow J clear P hp pr sr jr p grade order he,stocks]
    with m offer budget
  intro N interior per ref o v b H q η T G' eG gG L eL u earlier W k Q B D C s f a K P₀ cost front second third retained transfer range active
  let c:=R.family.side m per
  let n:=R.family.side k per
  let μ:=law P r T B
  let U:=state (G:=G) T B
  letI:IsFiniteMeasure μ:=funded P r T B hp pr sr
  have eF (i:Fin 2):Envelope (fun z:Config G c × Config G n=>f i z.1 z.2):=
    WilsonRegisteredHeldMoment.centered_joint R interior.le ref (v i) (o i) (η i)
  have eH:Envelope (fun z:Config G c × Config G n=>G' z.2):=
    ⟨eG.meas.comp measurable_snd,eG.cost.choose,fun z=>eG.cost.choose_spec z.2⟩
  have eP:Envelope (fun z:Config G c × Config G n=>P₀ z.1 z.2):=eH.mul ((eF 0).mul (eF 1))
  have eC:Envelope (fun z:Config G c × Config G n=>cost z.1 z.2):=(absolute eH).mul
    ((((Envelope.const (K 0)).mul (absolute (eF 1))).add ((Envelope.const (K 1)).mul (absolute (eF 0)))).add
      (Envelope.const (K 0*K 1)))
  have mc:MeasurableSet (cold R m per d o):=MeasurableSet.iInter (fun _=>House.bath _)
  have ms:MeasurableSet C:=mc.inter
    (MeasurableSet.iInter fun i=>visible R m per o (o i) (H i))
  have enroll (F:Config G c × Config G n→ℝ) (e:Envelope F):
      Envelope (fun V=>actualAverage R.family (N:=N) (C.indicator (fun X=>F (V,X))) V):=
    WilsonRegisteredHeldMoment.observed R interior.le (WilsonRegisteredHeldMoment.enclosed R C ms e)
  have first:Envelope front:=enroll _ eP
  have sb:Envelope second:=enroll _ (absolute eP)
  have tb:Envelope third:=enroll _ eC
  have mt:=WilsonCoherentHeldField.joined R interior grade (budget N per interior) T B
  have ma (i:Fin 2):Measurable (fun z:Config G c × Sample T B G=>a i z.1 z.2):=
    WilsonRegisteredHeldMoment.filed_joint R interior.le ref (v i) (o i) (b i) (q i) T B (η i)
  have mg:Measurable (fun z:Config G c × Sample T B G=>G' (U z.2)):=
    eG.meas.comp ((measurable_state T B).comp measurable_snd)
  let ν:=μ.restrict s
  letI : IsFiniteMeasure ν:=by dsimp only [ν];infer_instance
  letI : SFinite ν:=finite_kernel ν
  have rate:Measurable retained:=(((mt.mul mg).mul ((ma 0).mul (ma 1))).stronglyMeasurable.integral_prod_right' (ν:=ν)).measurable
  let δ:=ε*regulatorRun R.family N per k^p
  have small (V):|front V-retained V| ≤δ*second V+2*third V:=offer N interior per ref o v b H q η T V G' eG gG range active
  have gp:0≤regulatorRun R.family N per k:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have ep:0≤δ:=mul_nonneg he.le (pow_nonneg gp _)
  have er:=received first sb tb rate ep (by norm_num : (0:ℝ)≤2) small
  apply WilsonCoherentEarlier.signed R.family R.makes ((Nat.le_succ m).trans interior.le)
    (eL.mul first) (eL.mul er) ((absolute eL).mul sb) ((absolute eL).mul tb) _ earlier W
  intro V
  rw [←mul_sub,abs_mul]
  exact (mul_le_mul_of_nonneg_left (small V) (abs_nonneg _)).trans_eq (by ring)

end YM.Integration.WilsonRegisteredCenteredEarlier
end
