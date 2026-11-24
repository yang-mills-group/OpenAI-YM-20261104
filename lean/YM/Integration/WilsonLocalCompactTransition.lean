import YM.Integration.WilsonLocalCompactPosterior

/-! The funded compact retained operator is a contraction on bounded
signed physical inputs. Its kernel can act on the next retained output
without an extra gauge-invariance assumption on that output. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactTransition
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonCoherentForestReadout WilsonPhysicalRegisteredForestAction
open WilsonCoherentForestMeasure WilsonLocalRetainedCompactFibre WilsonLocalCompactPosteriorWeight
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G) {N per m:ℕ}

def send (live:m+1<N) (grade:ℕ) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (B:Finset T.Free) (H:Config G (R.family.side (m+1) per)→ℝ) (V:Config G (R.family.side m per)):ℝ:=
  let a:=amount R live grade T B V
  (∫u,a u*H (T.drape u) ∂T.order G)/(∫u,a u ∂T.order G)

private theorem joint (live:m+1<N) (grade:ℕ) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (B:Finset T.Free) (off:Measurable (approximation R (p:=per) live grade).eval):
    Measurable (fun z:Config G (R.family.side m per)×T.Slice G=>amount R live grade T B z.1 z.2):=by
  let X:=fun u:T.Slice G=>T.drape u
  let v:=fun u:T.Slice G=>((cut T (moving T B)) u).2
  have mx:Measurable X:=T.continuous_drape.measurable
  have mv:Measurable v:=measurable_snd.comp (cut T (moving T B)).measurable
  have origin:Measurable (fun u:T.Slice G=>state (G:=G) T B (v u,0)):=(measurable_state T B).comp (mv.prodMk measurable_const)
  have mq:=((R.family.path.rep N per (m+1)).envelope (R.makes.wilson.represents N per (m+1) live.le).good).meas
  have core:=((R.family.path.levels.clock.op m per).density_meas (R.family.path.levels.blocks m per).branches
    (R.family.path.β N per (m+1))).comp ((mx.comp measurable_snd).prodMk measurable_fst)
  exact core.mul ((((mq.comp origin).div (off.comp origin)).comp measurable_snd).mul ((off.comp mx).comp measurable_snd))

private theorem prob {X Y:Type} [MeasurableSpace X] [MeasurableSpace Y] (ν:Measure X)
    {P:Y→X→ℝ} (mass:∀y,Integrable (P y) ν ∧ 0<(∫x,P y x ∂ν) ∧ ∀x,0≤P y x)
    {h f:X→ℝ} (eh:Envelope h) (ef:Envelope f) {c:ℝ} (bound:∀x,|h x-f x|≤c) (y:Y):
    let Z:=∫x,P y x ∂ν
    |(∫x,P y x*h x ∂ν)/Z-(∫x,P y x*f x ∂ν)/Z| ≤ c := by
  intro Z
  obtain ⟨ip,pz,nn⟩:=mass y
  have each {H:X→ℝ} (en:Envelope H):Integrable (fun x=>P y x*H x) ν:=by
    have top:=ip.mul_const en.cost.choose
    exact top.mono' ((ip.aestronglyMeasurable.mul en.meas.aestronglyMeasurable)) (Eventually.of_forall fun x=>by
      rw [norm_mul,Real.norm_eq_abs (P y x),abs_of_nonneg (nn _)]
      exact mul_le_mul_of_nonneg_left (en.cost.choose_spec _) (nn _))
  have i1:=each eh
  have i2:=each ef
  rw [←sub_div,←integral_sub i1 i2,abs_div,abs_of_pos pz]
  apply (div_le_iff₀ pz).2
  calc |∫x,P y x*h x-P y x*f x ∂ν| ≤∫x,‖P y x*h x-P y x*f x‖ ∂ν:=by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x=>P y x*h x-P y x*f x)
    _ ≤∫x,P y x*c ∂ν:=integral_mono (i1.sub i2).norm (ip.mul_const _) fun x=>by
      rw [←mul_sub,Real.norm_eq_abs,abs_mul,abs_of_nonneg (nn _)]
      exact mul_le_mul_of_nonneg_left (bound x) (nn _)
    _=c*Z:=by rw [integral_mul_const,mul_comm]

def Funded (N per m:ℕ) (K:(Config G (R.family.side (m+1) per)→ℝ) → Config G (R.family.side m per)→ℝ) (δ:ℝ):Prop:=
  (∀H,Envelope H→Envelope (K H)) ∧
  (∀H h,Envelope H→Envelope h→∀C:ℝ,(∀U,|H U-h U|≤C)→∀V,|K H V-K h V|≤C) ∧
  (∀H,Envelope H→GaugeInvariant H→∀C:ℝ,(∀U,|H U|≤C)→∀V,|K H V-actualAverage R.family (N:=N) H V|≤2*(δ*(1+δ))*C)

theorem original (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
      (T:Forest (R.family.path.levels.clock.op m per).ratio),
    Funded R N per m (send R live grade T (incident R T d o)) (ε*regulatorRun R.family N per (m+1)^q) := by
  have calendar:=(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)
  filter_upwards [calendar,WilsonLocalCompactPosteriorWeight.fields R simple marks fees slow d q grade ord ep,
    WilsonLocalCompactPosterior.original R simple marks fees slow d q grade ord ep] with i offer weights law N live per o T
  let B:=incident R T d o
  let a:=amount R live grade T B
  let μ:=T.order G
  let K:=send R live grade T B
  let δ:=ε*regulatorRun R.family N per (i+1)^q
  have unit (V):=law N live per o T V (fun _=>1) (Envelope.const 1) (fun _ _=>rfl)
  have nonneg (V u):0≤a V u:=by
    rw [show a V u=_ from cancel R live grade T B V u]
    exact mul_nonneg (Multi.AxisShift.chosen_positive R.makes.wilson (by omega) V).le ((weights N live per o T V).2 u).2.1
  have mass (V):Integrable (a V) μ ∧ 0<(∫u,a V u ∂μ) ∧ ∀u,0≤a V u:=⟨(unit V).1,(unit V).2.2.1,nonneg V⟩
  have raised {H:Config G (R.family.side (i+1) per)→ℝ} (e:Envelope H):Envelope (fun u:T.Slice G=>H (T.drape u)):=
    ⟨e.meas.comp T.continuous_drape.measurable,e.cost.choose,fun u=>e.cost.choose_spec (T.drape u)⟩
  have contraction (H h:Config G (R.family.side (i+1) per)→ℝ) (eh:Envelope H) (ef:Envelope h) (C:ℝ)
      (bound:∀U,|H U-h U|≤C) (V):|K H V-K h V|≤C:=prob μ mass (raised eh) (raised ef) (fun u=>bound (T.drape u)) V
  have measured:=joint R live grade T B (OriginalMarkedRunCovariance.keep_envelope R live (offer N per live)).meas
  letI:IsProbabilityMeasure μ:=inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _:T.Free=>G.probHaar))
  refine ⟨fun H eh=>?_,contraction,fun H eh gh C bound V=>?_⟩
  · let Z:=fun V=>∫u,a V u ∂μ
    have zm:Measurable Z:=measured.stronglyMeasurable.integral_prod_right' (ν:=μ) |>.measurable
    have wh:Measurable (fun z:Config G (R.family.side i per)×T.Slice G=>a z.1 z.2*H (T.drape z.2)):=
      measured.mul ((eh.meas.comp T.continuous_drape.measurable).comp measurable_snd)
    refine ⟨(wh.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable.div zm,eh.cost.choose,fun V=>?_⟩
    have zero:K (fun _=>0) V=0:=by simp [K,send]
    have estimate:=contraction H (fun _=>0) eh (Envelope.const 0) eh.cost.choose (fun U=>by simpa [Real.norm_eq_abs] using eh.cost.choose_spec U) V
    simpa only [zero,sub_zero,Real.norm_eq_abs] using estimate
  · let v:=actualAverage R.family (N:=N) H V
    have vc:|v|≤C:=by simpa only [Real.norm_eq_abs] using actualAverage_norm_le R.family R.makes live.le (F:=H) (fun U=>by simpa only [Real.norm_eq_abs] using bound U) V
    have centered:∀U,‖|H U-v|‖≤2*C:=fun U=>by
      rw [Real.norm_eq_abs,abs_abs]
      exact (abs_sub (H U) v).trans ((add_le_add (bound U) vc).trans_eq (by ring))
    have used:=actualAverage_norm_le R.family R.makes live.le centered V
    have avg:actualAverage R.family (N:=N) (fun U=>|H U-v|) V≤2*C:=(le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using used)
    have dp:0≤δ:=mul_nonneg ep.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
    calc |K H V-v| ≤ δ*(1+δ)*actualAverage R.family (N:=N) (fun U=>|H U-v|) V:=(law N live per o T V H eh gh).2.2.2.2.2
         _ ≤ δ*(1+δ)*(2*C):=mul_le_mul_of_nonneg_left avg (mul_nonneg dp (by linarith))
         _=2*(δ*(1+δ))*C:=by ring

end YM.Integration.WilsonLocalCompactTransition
