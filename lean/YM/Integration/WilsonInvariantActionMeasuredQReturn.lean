import YM.Integration.ManuscriptQLocalOriginalMaskRate
import YM.Integration.WilsonInvariantActionPreviousQTariff
import YM.Integration.WilsonInvariantActionTransportedOld
import YM.Integration.WilsonRegisteredAxialEarlier

/-! The full conditional log on an incoming physical source against an earlier measured
grade-four regular terms, with original transport to every coarser measured date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionMeasuredQReturn
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker OPE.Therm Comparison.RG02
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Pert.Asymptotics
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalRegularConditional ManuscriptQLocalSourceFourier
open RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations Source RG3.Script.Picnic PhysicalNext.ThroughLaunch WilsonLimitConstruction
open Actual Order IterationFour IterationFour.Vacuum
open WilsonInvariantActionTransportedOld WilsonInvariantActionMixedMaterial
open RG16 PertExtension Tree Precision RG17 RG12 Extraction Spec OPE Table SharpGram.Lenses Pier.Lair Overlay PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}
  (R:Run G) (J:Request V) (A:NumericSchedule R.family J)
variable {f:Extraction.Order} {S:Table R.family.book} (Φ:Spec.Final R.family f S) (L:RG17.Layout Φ)
  (E:OPE.Services R.family f S)

private theorem carried {k N p:ℕ} (live:k≤N)
    (F:Config G (R.family.side k p)→ℂ) (hf:Envelope F) {i:ℕ} (hi:i≤k):
    Envelope (actualTransport R.family (N:=N) F hi):=by
  induction hi using Nat.decreasingInduction with
  | self=>rw [actualTransport_base R.family R.makes live];exact hf
  | of_succ j hj ih=>rw [actualTransport_step R.family R.makes live _ hj]
                     exact WilsonForwardMeasurable.average R.makes (hj.trans_le live) ih

set_option backward.isDefEq.respectTransparency false in
include E in
theorem original (simple:G.Simple) (warm:Poetry R.family.path.levels)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (q h H:ℕ) {ε:ℝ} (positive:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀(d:LocalFormal.Datum R.family Γ),d.level=m→
    ∀(F:AnalyticInput J A d) (x:IndependentTests J.tests) (s:Γ.Mode),
      let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
      let B:=(R.family.path.rep d.cutoff d.period (d.level+1)).p
      let w:=fun v=>F.inputRadii v/F.kernelCosts v
      let X:=F.packets.read (testInclusion J.tests x) g
      let Y:=ManuscriptQLocalOriginalConditionalTail.source F.packets B g x 1
      let ℒ T:=ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=d.cutoff) T
      let change:=fun U=>(Poly.toll w s:ℂ)*((ℒ X U).part s-(ℒ Y U).part s)
      let μ:=scene R.family.path d.cutoff d.period d.level
      Integrable change μ ∧
        (∀(u:ℕ) (held:u≤d.level), (∫W,‖actualTransport R.family (N:=d.cutoff) change held W‖
          ∂scene R.family.path d.cutoff d.period u)≤2*g^(q+2*(h+H*(4+1)+1)+1)) ∧
        ∀(r:ℝ) (w₀:R.family.label 4) (M:ℝ), 0≤M →
          R.family.ref 4≤L.level r → L.level r≤d.level+1 →
          R.family.S.a (L.level r)/R.family.S.a (d.level+1)≤R.family.path.levels.clock.hatBeta (d.level+1)^H →
          mass R.family 4 (L.shift 4 r w₀)≤R.family.path.levels.clock.hatBeta (L.level r)^h*M →
          ∀(y:Site (R.family.side (d.level+1) d.period)) (I:Set ℕ),
          let v:=RG17.atRef L 4 r (d.cutoff,d.period) w₀
          let pair:=fun U=>change U*centered R (Nat.le_succ _) d.below v y I U
          Integrable pair μ ∧ (∫U,‖pair U‖ ∂μ)≤ε*g^q*M ∧
            ∀(u:ℕ) (earlier:u≤d.level), (∫W,‖actualTransport R.family (N:=d.cutoff) pair earlier W‖
                ∂scene R.family.path d.cutoff d.period u)≤ε*g^q*M:=by
  let K:=q+2*(h+H*(4+1)+1)+1
  have base:=ManuscriptQLocalRawMaskFlat.physical (Γ:=Γ) R simple warm A 0 K (show (0:ℝ)<2 by norm_num)
  have funds:=WilsonInvariantActionPreviousQTariff.reported R Φ L E simple slow q h H (show (0:ℝ)≤1+0 by norm_num) positive
  filter_upwards [base,funds] with m base funds
  intro d hm
  subst m
  intro F x s g B w X Y ℒ change μ
  let hot:=fun U=>Poly.price w (ℒ X U-ℒ Y U)
  letI:IsProbabilityMeasure μ:=probability (H:=R.family.path) (p:=d.period) R.makes.wilson d.below.le
  have capX T:=(ManuscriptQLocalOriginalFineMaskLoss.original_rows F.packets F.input_paid x T).2
  have capY T:=(ManuscriptQLocalOriginalFineMaskLoss.regular_rows F.packets F.input_paid x B T).2
  have Z T:=ManuscriptQLocalOriginalFineMaskLoss.means_quiet F.packets F.input_paid x B T
  have bx:=ManuscriptQLocalOriginalFineMaskLoss.full_borel F.packets x (g:=g)
  have bym:=ManuscriptQLocalOriginalFineMaskLoss.mask_borel F.packets x B (g:=g)
  have bx' :=ManuscriptQLocalMeasuredMarkTransport.measured_log R.family R.makes d.below X
    (ManuscriptQLocalMeasuredMarkTransport.env F.input_paid.positive R.family X bx capX) (fun T=>(Z T).1)
  have by' :=ManuscriptQLocalMeasuredMarkTransport.measured_log R.family R.makes d.below Y
    (ManuscriptQLocalMeasuredMarkTransport.env F.input_paid.positive R.family Y bym capY) (fun T=>(Z T).2)
  have hmeas:Measurable change:=
    measurable_const.mul (((Poly.get s).continuous.measurable.comp bx').sub ((Poly.get s).continuous.measurable.comp by'))
  have hint:Integrable hot μ:=by
    simpa only [pow_one] using ManuscriptQLocalMeasuredMarkTransport.finite_moment F.input_paid.positive R.family
      R.makes d.below X Y bx bym capX capY (fun T=>(Z T).1) (fun T=>(Z T).2) 1
  have member U:‖change U‖≤hot U:=by
    change ‖(Poly.toll w s:ℂ)*_‖≤_
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Poly.worth F.input_paid.positive s).le]
    exact Poly.member F.input_paid.positive s (ℒ X U-ℒ Y U)
  have earned:Integrable change μ:=hint.mono' hmeas.aestronglyMeasurable (ae_of_all _ member)
  have bin: (∫U,hot U ∂μ)≤2*g^K:=by simpa only [Nat.zero_add,pow_one] using base d rfl F x
  have before: (∫U,‖change U‖ ∂μ)≤2*g^K:= (integral_mono earned.norm hint member).trans bin
  refine ⟨earned,fun u held=>(ActualWilsonAbsoluteTransport.first R.family R.makes d.below.le
    (WilsonRegisteredAxialEarlier.raw R.makes d.below.le earned) held).trans before,?_⟩
  intro r w₀ M hM age later room shift y I v pair
  let c:=budget v (d.level+1) d.cutoff d.period
  have old:=WilsonInvariantActionMixedMaterial.filed R.makes d.below (age.trans later) v y I
  have cap:∀U,‖reading R (Nat.le_succ _) d.below v y I U‖≤c:=
    actualTransport_norm_le R.family R.makes d.below old.2.2.2 (Nat.le_succ _)
  have avg:‖∫U,reading R (Nat.le_succ _) d.below v y I U ∂μ‖≤c:=by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=μ) (ae_of_all _ cap)
  have wt:∀U,‖centered R (Nat.le_succ _) d.below v y I U‖≤2*c:=fun U=>
    (norm_sub_le _ _).trans ((add_le_add (cap U) avg).trans_eq (by ring))
  have meas:Measurable (centered R (Nat.le_succ _) d.below v y I):= (carried R d.below _ old.2.1 (Nat.le_succ _)).meas.sub measurable_const
  have joint:Integrable pair μ:=earned.mul_bdd meas.aestronglyMeasurable (ae_of_all _ wt)
  have nonneg:0≤2*c:= (norm_nonneg _).trans (wt 1)
  have total: (∫U,‖pair U‖ ∂μ)≤ε*g^q*M:=calc
    _≤∫U,(2*c)*hot U ∂μ:=by
      apply integral_mono joint.norm (hint.const_mul _)
      intro U
      change ‖pair U‖≤(2*c)*hot U
      rw [show ‖pair U‖=‖change U‖*‖centered R (Nat.le_succ _) d.below v y I U‖ from norm_mul _ _, mul_comm (2*c)]
      exact mul_le_mul (member U) (wt U) (norm_nonneg _) (Poly.nonnegative F.input_paid.positive _)
    _=(2*c)*∫U,hot U ∂μ:=integral_const_mul _ _
    _≤(2*c)*(2*g^K):=mul_le_mul_of_nonneg_left bin nonneg
    _≤ε*g^q*M:=by
      simpa only [add_zero,mul_one] using funds r d.cutoff d.period later d.below age room w₀ M hM shift
  refine ⟨joint,total,fun u earlier=>?_⟩
  exact (ActualWilsonAbsoluteTransport.first R.family R.makes d.below.le
    (WilsonRegisteredAxialEarlier.raw R.makes d.below.le joint) earlier).trans total

end YM.Integration.WilsonInvariantActionMeasuredQReturn
