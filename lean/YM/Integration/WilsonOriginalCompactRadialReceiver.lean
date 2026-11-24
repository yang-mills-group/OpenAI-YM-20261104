import YM.Integration.WilsonOriginalRadialCommonGrid
import YM.Integration.WilsonOriginalFiledBochner

/-! At any live finite date, the independently submitted compact wallet prices its
complete real radial derivative hearing on the original quiet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompactRadialReceiver
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

open MeasureTheory WilsonRootedKioskOccupiedSlip

open WilsonOriginalJointTrialHearing WilsonOriginalPhysicalRadialDerivative
open WilsonOriginalRadialCommonGrid
variable {G:Gauge}(R:Run G){N per K m k:ℕ}{V:Type}[DecidableEq V][Fintype V]{J:Census V}
local notation "H" => R.family.path
local notation "A" => R.family.params
local notation "X" j:max => Config G (R.family.side j per)
variable {π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}{Ψ:∀j,RG.Rep G (R.family.side j per)}

theorem paid (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(lo:m≤K)(live:K≤N)
    {Y ι:Type}[Countable ι]{bp:BudgetPoint}{o:V→Site (R.family.side K per)}
    (L:Lamps Y ι G bp o J){w:V→ℝ}(wp:∀v,0<w v){α C:ℝ}(apos:0≤α)(income:Gross L w bp.B α C)(y:Y):
    let Z:X K→Poly J:=fun U=>((Ψ K).eval U:ℂ) • Poly.pass (bare L y U)
    Integrable Z (prior G _) ∧ ∀s:J.Mode,∀U,‖face R (N:=N) Z s U‖≤
      (Poly.toll w s)⁻¹*WilsonReceivedWholeFieldHot.charge s C:=by
  intro Z
  refine ⟨WilsonOriginalOrdinaryBochner.unmasked (Ψ K) (WilsonOriginalFiledBochner.envelope R course lo live) L wp apos income y,?_⟩
  intro s U
  have cap:‖(Poly.pass (bare L y U)).part s‖≤(Poly.toll w s)⁻¹*WilsonReceivedWholeFieldHot.charge s C:=
    (le_inv_mul_iff₀ (Poly.worth wp s)).mpr (WilsonReceivedWholeFieldHot.ordinary L wp apos income y U s)
  have same:(Ψ K).eval=((H).rep N per K).eval:=(course.1.walk K lo live).view
  have pos:0<((H).rep N per K).eval U:=Multi.AxisShift.chosen_positive R.makes.wilson live U
  change ‖(((H).rep N per K).eval U:ℂ)⁻¹*(((Ψ K).eval U:ℂ)*(Poly.pass (bare L y U)).part s)‖≤_
  rw [same,←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr pos.ne'),one_mul]
  exact cap

theorem original (simple:G.Simple)(d P:ℕ)(F:Labels.Frame G d):
    ∀ᶠ i:ℕ in atTop,∀der≤d,∀a∈Push.Local.tests F,∀{N per m k K depth:ℕ}
      (_live:K≤N)(past:i<K),d≤depth → 1≤((H).levels.budget i).supportExponent →
      ∀{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}{Ψ:∀j,RG.Rep G (R.family.side j per)},
       Concourse R.alloy R.kit R.T π Γ m N per k Ψ → m≤K →
      ∀{Y ι:Type}[Countable ι]{bp:BudgetPoint}{o:V→Site (R.family.side K per)}
        (L:Lamps Y ι G bp o J){w:V→ℝ},(∀v,0<w v) →∀{α C:ℝ},0≤α → Gross L w bp.B α C → ∀(y:Y)(s:J.Mode),
       let Z:Config G (R.family.side K per)→Poly J:=fun U=>((Ψ K).eval U:ℂ) • Poly.pass (bare L y U)
       ∀(values:ℕ→ℂ)(E:ℝ),(∀j≤depth,‖read R N per (WilsonCapturedPrimaryWeakTrialRadial.field R d N per i (target d P) depth a j)
         past.le Z s-values j‖≤E) →
       let step:=Pert.Asymptotics.regulatorRun R.family N per (i+1)
       let B:=(H).levels.budget i
       let r:=radiusAt R (N:=N) (per:=per) (i:=i) d (target d P)
       let t:=step^(WilsonCapturedPrimaryPaid.gap (target d P) 1)*ratio der depth
       let M:=(Poly.toll w s)⁻¹*WilsonReceivedWholeFieldHot.charge s C
       let f:ℝ→ℂ:=fun x=>read R N per (WilsonCapturedPrimaryRays.field A B 0 r a x) past.le Z s
       ‖iteratedDeriv der f 0-WilsonOriginalRadialFiniteDifference.divided der t values‖≤
         WilsonCapturedPrimarySamples.price der*(E/t^der+WilsonOriginalRadialSpringTariff.factor H A a (der+1)*M*step^P):=by
  filter_upwards [WilsonOriginalRadialCommonGrid.original R simple d P F] with i all
  intro der dk a ha N per m k K depth live past dd price π Γ Ψ course lo Y ι ic bp o L w wp α C ap ink y s Z values E heard
  obtain ⟨intg,cap⟩:=paid R course lo live L wp ap ink y
  exact all der dk a ha live past dd price Z intg s _ ((norm_nonneg _).trans (cap s 1)) (cap s) values E heard

end YM.Integration.WilsonOriginalCompactRadialReceiver
