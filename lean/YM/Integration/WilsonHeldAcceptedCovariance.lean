import YM.Integration.WilsonAcceptedLinkWeight
import YM.Integration.WilsonHeldCenteredCovariance
import YM.Integration.WilsonForwardMeasurable

/-! On a measurable collection of actual upper fields, replace the conditional
action inside the inspected links at its original, exterior-dependent mass.
The other upper configurations, the lower field and the inherited observable
are carried by the original Wilson transition. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldAcceptedCovariance
open Set MeasureTheory Real Lattice RG Wilson PhysicalNext.Repeat.Legato
open WilsonCenteredHaarReading WilsonHeldExteriorLaw WilsonAcceptedLinkWeight
open private sampled shift translate change from YM.Integration.WilsonCenteredHaarReading
open private total from YM.Integration.WilsonHeldExteriorLaw
open scoped Classical
variable {G:Gauge} (R:Run G) {N per j:ℕ}
local notation "n" => R.family.side (j+1) per
local notation "Q" => R.family.path.rep N per (j+1)
local notation "ν" => prior G n

private theorem inherited {j:ℕ} (live:j≤N)
    (A:Config G (R.family.side N per)→ℂ) (a:Envelope A) :
    Envelope (actualTransport R.family (N:=N) A live) := by
  induction live using Nat.decreasingInduction with
  | self=>rw [actualTransport_base R.family R.makes le_rfl];exact a
  | of_succ k hk ih=>
    rw [actualTransport_step R.family R.makes le_rfl _ hk]
    exact WilsonForwardMeasurable.average R.makes hk ih

private theorem mixed {X:Type*} [MeasurableSpace X] (μ:Measure X) {p q:X→ℝ}
    (ep:Integrable p μ) (eq:Integrable q μ) (p1:∫x,p x ∂μ=1) (q1:∫x,q x ∂μ=1)
    {F B:X→ℂ} (ef:Envelope F) (eb:Envelope B) :
    let H:=fun x=>(F x-mean μ p F)*(B x-mean μ q B)
    cov μ p F B-cov μ q F B=∫x,(p x-q x) • H x ∂μ := by
  intro H
  let f:=fun x=>F x-mean μ p F
  let b:=fun x=>B x-mean μ q B
  have Z₁:mean μ p f=0:=(translate μ ep p1 ef _).trans (sub_self _)
  have Z₀:mean μ q b=0:=(translate μ eq q1 eb _).trans (sub_self _)
  rw [←shift μ ep p1 ef eb (mean μ p F) (mean μ q B),
    ←shift μ eq q1 ef eb (mean μ p F) (mean μ q B)]
  change (mean μ p H-mean μ p f*mean μ p b)-(mean μ q H-mean μ q f*mean μ q b)=_
  rw [Z₁,Z₀,zero_mul,mul_zero,sub_zero,sub_zero]
  exact change μ ep eq (product (centered ef _) (centered eb _))

/-- One error integral for the whole earlier/fresh covariance at a held
lower field. Its two means are taken after reassembling the genuine exterior
law. The bound only charges the originally accepted upper fields. -/
theorem original (live:j+1≤N) (V:Config G (R.family.side j per))
    (fixed:Set (Edge (Site n))) (E:Set (Config G n)) (event:MeasurableSet E)
    (Y:Config G n→ℝ) (envelope:Envelope (fun U=>exp (Y U)))
    (A:Config G (R.family.side N per)→ℂ) (B:Config G n→ℂ) (ha:Envelope A) (hb:Envelope B)
    {δ:ℝ} (nonneg:0≤δ) :
    let q:=weight R N per j V Q
    let p:=fun U=>q U*(exp (Y U)/(Q).eval U)
    let w:=redraw fixed E q p
    let F:=actualTransport R.family (N:=N) A live
    let H:=fun U=>(F U-mean ν w F)*(B U-mean ν q B)
    (∀U∈E,∀U'∈E,((cut G fixed) U).1=((cut G fixed) U').1 →
      |(Y U'-log ((Q).eval U'))-(Y U-log ((Q).eval U))|≤δ) →
    (∀u,mass fixed E w u=mass fixed E q u) ∧
    (∀u,marginal fixed w u=marginal fixed q u) ∧
    cov ν w F B-WilsonHeldPriorCovariance.connected R.family (N:=N) F B V=
      ∫U,(w U-q U) • H U ∂ν ∧
    ‖cov ν w F B-WilsonHeldPriorCovariance.connected R.family (N:=N) F B V‖≤
      (exp δ-1)*∫U,E.indicator q U*‖H U‖ ∂ν := by
  intro q p w F H osc
  obtain ⟨a,apos,floor⟩:=upper_floor R N per j live
  have qe:=(Q).envelope (R.makes.wilson.represents N per (j+1) live).good
  obtain ⟨hq,c,cpos,cap⟩:=regularity R N per j live V Q qe apos floor
  have qn:∀U,0≤q U:=fun U=>cpos.le.trans (cap U)
  have Qpos:∀U,0<(Q).eval U:=fun U=>apos.trans_le (floor U)
  have ratio:Envelope (fun U=>exp (Y U)/(Q).eval U):=by
    obtain ⟨M,hi⟩:=envelope.cost
    refine ⟨envelope.meas.div qe.meas,M/a,fun U=>?_⟩
    rw [Real.norm_eq_abs,abs_of_pos (div_pos (exp_pos _) (Qpos U))]
    exact (div_le_div_of_nonneg_left (exp_pos _).le apos (floor U)).trans
      (div_le_div_of_nonneg_right ((le_abs_self _).trans (hi U)) apos.le)
  have hp:Envelope p:=hq.mul ratio
  have factor:∀U∈E,p U=q U*exp (Y U-log ((Q).eval U)):=fun U _=>by
    simp only [p,exp_sub,exp_log (Qpos U)]
  have var:=variation fixed E event q p (fun U=>Y U-log ((Q).eval U)) hq hp qn factor nonneg
    (fun U eu W ew same=>osc W ew U eu same.symm)
  obtain ⟨hw,out⟩:=full fixed E event q p hq hp (sub_nonneg.mpr (one_le_exp nonneg)) var
  have hq1:∫U,q U ∂ν=1:=actualConditionalDensity_total R.family R.makes live V
  have hw1:∫U,w U ∂ν=1:=by
    rw [←total fixed (hw.integrable ν),funext out,total fixed (hq.integrable ν),hq1]
  have ef:Envelope F:=inherited R live A ha
  have he:Envelope H:=product (centered ef _) (centered hb _)
  have iscov:WilsonHeldPriorCovariance.connected R.family (N:=N) F B V=cov ν q F B:=
    WilsonHeldPriorCovariance.original R.family F B V (sampled ν (hq.integrable ν) ef)
      (sampled ν (hq.integrable ν) (product ef hb))
  have id:=mixed ν (hw.integrable ν) (hq.integrable ν) hw1 hq1 ef hb
  rw [iscov,id]
  refine ⟨slice fixed E q p,out,rfl,?_⟩
  have integr:Integrable (fun U=>E.indicator q U*‖H U‖) ν:=by
    obtain ⟨M,bd⟩:=he.cost
    apply Integrable.mono' ((hq.integrable ν).indicator event |>.norm.mul_const M)
      (((hq.meas.indicator event).mul he.meas.norm).aestronglyMeasurable)
    apply ae_of_all;intro U
    change ‖E.indicator q U*‖H U‖‖≤‖E.indicator q U‖*M
    rw [norm_mul,Real.norm_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (bd U) (abs_nonneg _)
  calc
    _≤∫U,‖(w U-q U) • H U‖ ∂ν:=norm_integral_le_integral_norm _
    _≤∫U,(exp δ-1)*(E.indicator q U*‖H U‖) ∂ν:=by
      apply integral_mono_of_nonneg (ae_of_all _ fun U=>norm_nonneg _) (integr.const_mul _)
      apply ae_of_all;intro U
      change ‖(w U-q U) • H U‖≤(exp δ-1)*(E.indicator q U*‖H U‖)
      rw [norm_smul,Real.norm_eq_abs,←mul_assoc]
      exact mul_le_mul_of_nonneg_right (var U) (norm_nonneg _)
    _=_:=integral_const_mul _ _
end YM.Integration.WilsonHeldAcceptedCovariance
end
