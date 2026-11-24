import YM.Integration.WilsonOriginalFlatHaloRate
import YM.Integration.WilsonOriginalDecoderPosterior

/-! Price native failed halos at a real retained Wilson field with its actual final spring. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalDecoderHaloRate
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open scoped BigOperators Classical

variable {G:Gauge}(R:Run G){N per m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (cut:b<N){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "Space" => Config G (R.family.side b per)




include course cut way ticket floor ub fixed S A in
theorem original (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(p d₀:ℕ){tol:ℝ}(positive:0<tol)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple (p+d₀) positive)).choose ≤ b)
    {ι:Type*}[DecidableEq ι](seats:Finset ι)(y:ι→Site (R.family.side b per))
    {α:ℝ}(strength:(Ψ b).p.supportExponent≤α)(Y:Space→ℂ)(borel:Measurable Y)
    {e B:ℝ}(ep:0≤e)(bp:0≤B)(gross:∀U,‖Y U‖ ≤ B*β^d₀)
    (clear:∀U,(∀a∈seats,Healthy (Ψ b).p.threshold (halo (Ψ b).p.B {y a}) U)→‖Y U‖≤e)
    {i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b)(W:Config G (R.family.side i per)):
    ‖actualTransport R.family (N:=N) Y ((Nat.le_succ i).trans ib) W‖ ≤
      e+B*(seats.card:ℝ)*(4*Real.exp (α+2))*tol/β^p*
        (Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per)
          (R.family.path.β N per (i+1)) W))^2:=by
  classical
  let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per ib W
  let μ₀:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per ib 1
  let T:=Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per)
    (R.family.path.β N per (i+1)) W)
  let E:Set Space:={U|e<‖Y U‖}
  let X:=E.indicator (fun _=>(1:ℂ))
  have hm:MeasurableSet E:=measurableSet_lt measurable_const borel.norm
  have hx:Measurable X:=measurable_const.indicator hm
  letI:IsProbabilityMeasure (scene R.family.path N per b):=probability R.makes.wilson cut.le
  letI:IsProbabilityMeasure μ:=WilsonMacroscopicRichFlatPosteriorLaw.prob R ib cut.le W
  have hX:Integrable X (scene R.family.path N per b):=(integrable_const _).indicator hm
  have node:=WilsonOriginalFlatHaloRate.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed
    capture (p+d₀) 0 positive (by simpa only [Nat.add_zero] using late) seats y strength X hx
    (e:=0) (B:=1) le_rfl zero_le_one
    (fun U=>by by_cases h:U∈E <;> simp [X,h])
    (fun U healthy=>by have h:U∉E:=not_lt.mpr (clear U healthy);simp [X,h]) ui ib
  rw [WilsonOriginalFailedHaloPosterior.flat R ib cut.le X hX] at node
  have flat:μ₀.real E ≤ (seats.card:ℝ)*(4*Real.exp (α+2))*tol/β^(p+d₀):=by
    simpa only [X,integral_indicator_const _ hm,Complex.real_smul,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg,one_mul,zero_add] using node
  have fee:μ.real E ≤ T^2*((seats.card:ℝ)*(4*Real.exp (α+2))*tol/β^(p+d₀)):=
    (WilsonOriginalDecoderPosterior.original R ib cut.le W hm).trans
      (mul_le_mul_of_nonneg_left flat (sq_nonneg T))
  have hb:0<β:=zero_lt_one.trans (R.alloy.B.a.fits.delayed b)
  have nonneg:=mul_nonneg bp (pow_nonneg hb.le d₀)
  have hY:Integrable Y (scene R.family.path N per b):=
    Integrable.of_bound borel.aestronglyMeasurable _ (ae_of_all _ gross)
  rw [←congrFun (WilsonSeparatedOriginalPosteriorTransport.realized (C:=R.family) (N:=N) (p:=per)
    R.makes cut.le ((Nat.le_succ i).trans ib) Y hY) W,
    WilsonMacroscopicRichFlatPosteriorLaw.reading R ib cut.le W Y hY]
  have bound:=WilsonOriginalFailedHaloPosterior.envelope μ ({()}:Finset Unit) (fun _=>E)
    (fun _ _=>hm) _ (fun _ _=>fee) Y borel ep nonneg gross
    (fun U h=>le_of_not_gt (h () (by simp)))
  apply bound.trans_eq
  simp only [Finset.sum_singleton,pow_add]
  change e+_ = e+_*T^2
  field_simp [hb.ne']

end YM.Integration.WilsonOriginalDecoderHaloRate
end
