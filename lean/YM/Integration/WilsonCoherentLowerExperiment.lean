import YM.Integration.WilsonCoherentHeldField
import YM.Integration.WilsonCoherentEarlier

/-! Test the retained signed marked experiment through any earlier original Wilson conditional. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCoherentLowerExperiment
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open RG16 ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction Pert.Asymptotics
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonIncidentRegisteredMass WilsonCoherentMeasuredStencil WilsonCoherentMeasuredChart
open scoped Classical Topology

private theorem absolute {X:Type*} [MeasurableSpace X] {f:X→ℝ} (e:Envelope f):Envelope (fun x=>|f x|):=
  ⟨e.meas.abs,e.cost.imp fun _ b u=>by simpa only [Real.norm_eq_abs,abs_abs] using b u⟩

private theorem cut {X:Type*} [MeasurableSpace X] {f:X→ℝ} (e:Envelope f) {s:Set X} (hs:MeasurableSet s):
    Envelope (s.indicator f) := by
  obtain ⟨c,h⟩:=e.cost
  refine ⟨e.meas.indicator hs,max 0 c,fun x=>?_⟩
  by_cases H:x∈s
  · simpa only [indicator_of_mem H] using (h x).trans (le_max_right 0 c)
  · simpa only [indicator_of_notMem H,norm_zero] using le_max_left (0:ℝ) c

private theorem received {X:Type*} [MeasurableSpace X] {f a b h:X→ℝ} (ef:Envelope f)
    (ea:Envelope a) (eb:Envelope b) (mh:Measurable h) {c d:ℝ} (cp:0≤c) (dp:0≤d)
    (price:∀x, |f x-h x|≤c*a x+d*b x) : Envelope h := by
  obtain ⟨F,hF⟩:=ef.cost
  obtain ⟨A,hA⟩:=ea.cost
  obtain ⟨B,hB⟩:=eb.cost
  refine ⟨mh,F+(c*A+d*B),fun x=>?_⟩
  have hf:=hF x
  have ha:=hA x
  have hb:=hB x
  simp only [Real.norm_eq_abs] at hf ha hb ⊢
  calc |h x| ≤ |h x-f x| + |f x| :=by simpa only [sub_add_cancel] using abs_add_le (h x-f x) (f x)
       _ = |f x|+|f x-h x| :=by rw [abs_sub_comm (h x) (f x),add_comm]
       _ ≤ F+(c*A+d*B):=add_le_add hf ((price x).trans (add_le_add
         (mul_le_mul_of_nonneg_left ((le_abs_self _).trans ha) cp)
         (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) dp)))

variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]
local notation "A" => R.family.path

theorem measured (simple:G.Simple) (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A).levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P)
    (d:I→ℕ) (q grade:ℕ) (order:q+5≤grade) {ε:ℝ} (he:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀N (interior:m+1<N) per (y:∀i,R.family.label (d i)) (o:I→Site (R.family.side (m+1) per))
    (T:Forest ((A).levels.clock.op m per).ratio) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (H:Config G (R.family.side (m+1) per)→ℝ),
    Envelope H → GaugeInvariant H → ∀ (L : Config G (R.family.side m per) → ℝ), Envelope L →
    ∀ (u : ℕ) (lu : u ≤ m) (V : Config G (R.family.side u per)),
    let B:=incident R T d o
    let θ:=((A).rep N per (m+1)).p.threshold
    let C:=cold R m per d o
    let F (U:Config G (R.family.side (m+1) per)):=χ (c*∏i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U)
    let δ:=ε*regulatorRun R.family N per (m+1)^q
    let K:=(‖χ‖*‖c‖)*(δ*originalMass R d y)
    let Tq (W:Config G (R.family.side m per)):=∫z in panel R m per d o T r,
      WilsonCoherentRetainedDriver.value R interior grade T B W z*H (state T B z)*
        χ (c*polynomial T B R d θ y o (q+2*reserve R d) z) ∂law P r T B
    let S0 (h:Config G (R.family.side (m+1) per)→ℝ):=actualAverage R.family (N:=N) (C.indicator h)
    let past (h:Config G (R.family.side m per)→ℝ):=actualTransport R.family (N:=N) h lu V
    |past (fun W=>L W*S0 (fun U=>H U*F U) W)-past (fun W=>L W*Tq W)|≤
      δ*past (fun W=>|L W| *S0 (fun U=>|H U*F U|) W)+2*K*past (fun W=>|L W| *S0 (fun U=>|H U|) W) := by
  have offered:= (tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [offered,WilsonCoherentMeasuredStencil.on_event R d simple,
    WilsonCoherentRetainedExperiment.measured R simple marks fees slow J clear P hp pr sr d q grade order he]
    with m offer same price N interior per y o T c χ H eH gH L eL u earlier V
  intro B θ C F δ K Tq S0 past
  let f:=mark R d o θ y c χ
  let U:=state (G:=G) T B
  let a:=fun z:Sample T B G=>χ (c*polynomial T B R d θ y o (q+2*reserve R d) z)
  have ma:Measurable a:=χ.continuous.measurable.comp ((measurable_polynomial T B R d θ y o (q+2*reserve R d)).const_mul c)
  have coeff:=WilsonCoherentHeldField.reading R interior grade (offer N per interior) T B P hp pr sr (panel R m per d o T r)
    ((eH.meas.comp (measurable_state T B)).mul ma)
  have mt:Measurable Tq:=by simpa only [Tq,a,mul_assoc,Pi.mul_apply,Function.comp_apply] using coeff
  have Cmeas:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  have sameF (U) (hu:U∈C):F U=f U:=congrArg (fun x:ℂ=>χ (c*x)) (same N per interior.le o y U hu).symm
  have eqs (D:ℝ→ℝ) : C.indicator (fun U=>D (H U*F U))=C.indicator (fun U=>D (H U*f U)):=by
    funext U
    by_cases hu:U∈C
    · rw [indicator_of_mem hu,indicator_of_mem hu,sameF U hu]
    · rw [indicator_of_notMem hu,indicator_of_notMem hu]
  have first:=eqs id
  simp only [id_eq] at first
  let f0:=S0 (fun U=>H U*F U)
  let f1:=S0 (fun U=>|H U*F U|)
  let f2:=S0 (fun U=>|H U|)
  have truth:=eH.mul (legitimate R d o θ y c χ).1
  have front:Envelope f0:=by
    dsimp only [f0,S0]
    rw [first]
    exact WilsonCoherentEarlier.averaged R.family R.makes interior.le (cut truth Cmeas)
  have strong:Envelope f1:=by
    dsimp only [f1,S0]
    rw [eqs abs]
    exact WilsonCoherentEarlier.averaged R.family R.makes interior.le (cut (absolute truth) Cmeas)
  have plain:Envelope f2:=WilsonCoherentEarlier.averaged R.family R.makes interior.le (cut (absolute eH) Cmeas)
  have paid (W):|f0 W-Tq W|≤δ*f1 W+2*K*f2 W:=price N interior per y o T W c χ H eH gH
  have g0:0≤regulatorRun R.family N per (m+1):=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have d0:0≤δ:=mul_nonneg he.le (pow_nonneg g0 q)
  have m0:0≤originalMass R d y:=Finset.prod_nonneg fun i _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have k0:0≤2*K:=by dsimp only [K];positivity
  have checked:=received front strong plain mt d0 k0 paid
  apply WilsonCoherentEarlier.signed R.family R.makes ((Nat.le_succ m).trans interior.le) (eL.mul front) (eL.mul checked)
    ((absolute eL).mul strong) ((absolute eL).mul plain) _ earlier V
  intro W
  rw [←mul_sub,abs_mul]
  exact (mul_le_mul_of_nonneg_left (paid W) (abs_nonneg _)).trans_eq (by ring)

end YM.Integration.WilsonCoherentLowerExperiment
