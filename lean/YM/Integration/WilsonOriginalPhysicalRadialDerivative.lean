import YM.Integration.WilsonOriginalRadialFiniteDifference
import YM.Integration.WilsonOriginalRegularComponent

/-! Differentiate the whole original face on its own normalized Haar descent. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalRadialDerivative
open Function Finset Filter Set MeasureTheory Labels Lattice Wilson RG Source Push.Local
open Marker Multi RG01.Kernel Next.Foundations Filter Pert.Asymptotics
open PhysicalNext.Repeat.Legato Stationary Comparison.RG02 Planned.AtomRegular
open WilsonCapturedPrimaryCollar WilsonCapturedPrimaryPaid WilsonCapturedPrimaryAngles
open WilsonOriginalJointTrialHearing WilsonFirstReceivedRadialStencil
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}(R:Run G){N per i K:ℕ}{V:Type}[DecidableEq V]{J:Census V}
local notation "H" => R.family.path
local notation "X" j:max => Config G (R.family.side j per)
local notation "μ" => prior G (R.family.side (i+1) per)
local notation "b" => (H).levels.budget i
local notation "g" => regulatorRun R.family N per (i+1)

def face (Z:X K→Poly J)(s:J.Mode)(U:X K):ℂ:=
  (((H).rep N per K).eval U:ℂ)⁻¹*(Z U).part s

private theorem conditioned (live:i<N)(F:X (i+1)→ℂ) {M:ℝ}
    (meas:AEStronglyMeasurable F μ)(gross:∀U,‖F U‖≤M)(W:X i):
    RG01.Kernel.conditional H N i per W (fun _=>F)=actualAverage R.family (N:=N) F W:=by
  let w:=RG01.Kernel.expense H N i per W
  have payment:=RG01.Kernel.actual N H R.makes.wilson W live
  have exactCost:RG01.Kernel.Bounded μ (fun _:((H).levels.clock.op i per).Choices=>F) M:=⟨fun _=>meas,fun _=>gross⟩
  have mass (U:X (i+1)):∑ t,w t U=actualConditionalDensity R.family N per i W U:=by
    dsimp [w,RG01.Kernel.expense,RG01.Kernel.upper,actualConditionalDensity]
    rw [←Finset.sum_div,←Finset.sum_mul]
    rfl
  change ∑t,∫U,(w t U:ℂ)*F U ∂μ=∫U,actualConditionalDensity R.family N per i W U • F U ∂μ
  rw [←integral_finsetSum Finset.univ (fun t _=>payment.funds exactCost t)]
  apply integral_congr_ae
  filter_upwards with U
  rw [←Finset.sum_mul,←Complex.ofReal_sum,mass]
  rfl

theorem received (live:K≤N)(past:i<K)(Z:X K→Poly J)(enrolled:Integrable Z (prior G _))
    (s:J.Mode){M:ℝ}(gross:∀U,‖face R (N:=N) Z s U‖≤M):
    let F:=actualTransport R.family (N:=N) (face R (N:=N) Z s) past
    (RG01.Kernel.Bounded μ (fun _:((H).levels.clock.op i per).Choices=>F) M) ∧
    (fun W=>read R N per W past.le Z s)=fun W=>RG01.Kernel.conditional H N i per W (fun _=>F):=by
  intro F
  have cost:∀U,‖F U‖≤M:=actualTransport_norm_le R.family R.makes live gross past
  have regular:=((H).rep N per K).envelope (R.makes.wilson.represents N per K live).good
  have component:AEStronglyMeasurable (fun U=>(Z U).part s) (prior G _):=
    (Poly.get s).continuous.comp_aestronglyMeasurable enrolled.1
  have borel:AEStronglyMeasurable (face R (N:=N) Z s) (prior G _):=
    (Complex.continuous_ofReal.measurable.comp regular.meas).inv.aestronglyMeasurable.mul component
  have bm:=(actualTransport_integrable R.family R.makes live borel gross past).aestronglyMeasurable
  refine ⟨⟨fun _=>bm,fun _=>cost⟩,?_⟩
  funext W
  rw [conditioned R (past.trans_le live) F bm cost W]
  change _=actualAverage R.family (N:=N) (actualTransport R.family (N:=N) _ past) W
  rw [←actualTransport_step R.family R.makes live _ past]
  unfold WilsonOriginalJointTrialHearing.read actualTransport
  rw [congrFun (WilsonOriginalRegularComponent.projected R Z enrolled s past.le) W]
  rw [Complex.real_smul,Complex.ofReal_inv]
  congr 2
  funext U
  have pos:0<((H).rep N per K).eval U:=Multi.AxisShift.chosen_positive R.makes.wilson live U
  have nonzero:(((H).rep N per K).eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr pos.ne'
  change (Z U).part s=(((H).rep N per K).eval U:ℂ)*((((H).rep N per K).eval U:ℂ)⁻¹*(Z U).part s)
  rw [←mul_assoc,mul_inv_cancel₀ nonzero,one_mul]

def radiusAt (d target:ℕ):ℕ:=radius b (cutoff b g (grade target d 1))

theorem original (live:K≤N)(past:i<K)(Z:X K→Poly J)(enrolled:Integrable Z (prior G _))
    (s:J.Mode){M:ℝ}(gross:∀U,‖face R (N:=N) Z s U‖≤M)(mp:0≤M)
    (d target:ℕ)(a:Probe G d)(k:ℕ)(dk:k≤d)
    (unit:g^gap target 1≤1)
    (short:g^gap target 1*wallet R.family.params a (radiusAt R (N:=N) (per:=per) (i:=i) d target)≤1)
    (width:(b).threshold*(1+((radiusAt R (N:=N) (per:=per) (i:=i) d target):ℝ))^2≤1)
    (values:ℕ→ℂ){E:ℝ}
    (heard:∀j≤k,‖read R N per (WilsonCapturedPrimaryWeakTrialRadial.field R d N per i target k a j) past.le Z s-values j‖≤E):
    let r:=radiusAt R (N:=N) (per:=per) (i:=i) d target
    let t:=g^gap target 1
    let f:ℝ→ℂ:=fun x=>read R N per (WilsonCapturedPrimaryRays.field R.family.params b 0 r a x) past.le Z s
    let fee:=WilsonOriginalRadialSpringRemainder.bill H (N:=N) (i:=i) (p:=per) R.family.params b 0 r a (k+1) M
    ‖iteratedDeriv k f 0-WilsonOriginalRadialFiniteDifference.divided k t values‖≤
      WilsonCapturedPrimarySamples.price k*(E/t^k+fee*t):=by
  intro r t f fee
  obtain ⟨source,eqn⟩:=received R live past Z enrolled s gross
  let F:=actualTransport R.family (N:=N) (face R (N:=N) Z s) past
  have gp:0<g:=RG16.Literal.g_pos R.makes (past.trans_le live)
  have ident:f=WilsonOriginalRadialSpringRemainder.curve H (N:=N) R.family.params b 0 r a (fun _=>F):=by
    exact funext (fun z=>congrFun eqn _)
  rw [ident]
  apply WilsonOriginalRadialFiniteDifference.original H R.makes.wilson (past.trans_le live)
    (fun _=>F) source mp R.family.params b 0 r a k dk (pow_pos gp _) unit short width values
  intro j hj
  have nodeSame:WilsonCapturedPrimaryWeakTrialRadial.field R d N per i target k a j=
      WilsonCapturedPrimaryRays.field R.family.params b 0 r a (t*node k j):=by
    unfold WilsonCapturedPrimaryWeakTrialRadial.field WilsonCapturedPrimaryPotential.lifted
    rw [WilsonCapturedPrimaryPotential.sampled gp,WilsonCapturedPrimaryAngles.physical]
    rfl
  have h:=heard j hj
  rw [nodeSame] at h
  change ‖conditional H N i per (WilsonCapturedPrimaryRays.field R.family.params b 0 r a (t*node k j)) (fun _=>F)-values j‖≤E
  rw [←congrFun eqn _]
  exact h

end YM.Integration.WilsonOriginalPhysicalRadialDerivative
